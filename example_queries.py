from z3 import And, Not, Or

from config import ModelConfig
from model import make_solver
from plot import plot_model
from pyz3_utils import MySolver, run_query
from utils import make_periodic


def bbr_low_util(timeout=10):
    '''Finds an example trace where BBR has < 10% utilization. It can be made
    arbitrarily small, since BBR can get arbitrarily small throughput in our
    model.

    You can simplify the solution somewhat by setting simplify=True, but that
    can cause small numerical errors which makes the solution inconsistent. See
    README for details.

    '''
    c = ModelConfig.default()
    c.compose = True
    c.cca = "bbr"
    # Simplification isn't necessary, but makes the output a bit easier to
    # understand
    c.simplify = False
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # Ask for < 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    make_periodic(c, s, v, 2 * c.R)
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c, qres.v)


def bbr_test(timeout=10):
    c = ModelConfig.default()
    c.compose = True
    c.cca = "bbr"
    c.buf_min = 0.5
    c.buf_max = 0.5
    c.T = 8
    # Simplification isn't necessary, but makes the output a bit easier to
    # understand
    c.simplify = False
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # Ask for < 10% utilization. Can be made arbitrarily small
    #s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    s.add(v.L[-1] - v.L[0] >= 0.5 * (v.S[-1] - v.S[0]))
    s.add(v.A[0] == 0)
    s.add(v.r_f[0][0] < c.C)
    s.add(v.r_f[0][1] < c.C)
    s.add(v.r_f[0][2] < c.C)
    make_periodic(c, s, v, 2 * c.R)
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c, qres.v)


def copa_low_util(timeout=10):
    '''Finds an example where Copa gets < 10% utilization. This is with the default
    model that composes. If c.compose = False, then CCAC cannot find an example
    where utilization is below 50%. copa_proofs.py proves bounds on Copa's
    performance in the non-composing model. When c.compose = True, Copa can get
    arbitrarily low throughput

    '''
    c = ModelConfig.default()
    c.compose = False
    c.cca = "copa"
    c.simplify = False
    c.calculate_qdel = True
    c.unsat_core = False
    c.T = 10
    s, v = make_solver(c)
    # Consider the no loss case for simplicity
    s.add(v.L[0] == v.L[-1])
    # 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    make_periodic(c, s, v, c.R + c.D)

    print(s.to_smt2(), file = open("/tmp/ccac.smt2", "w"))
    s.check()
    print(s.statistics())
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c, qres.v)


def aimd_premature_loss(timeout=60):
    '''Finds a case where AIMD bursts 2 BDP packets where buffer size = 2 BDP and
    cwnd <= 2 BDP. Here 1BDP is due to an ack burst and another BDP is because
    AIMD just detected 1BDP of loss. This analysis created the example
    discussed in section 6 of the paper. As a result, cwnd can reduce to 1 BDP
    even when buffer size is 2BDP, whereas in a fluid model it never goes below
    1.5 BDP.

    '''
    '''
    Behrooz: Timing of this doesn't match timing presented in the paper. 
    Here we see query is satisfied at 5, and then cwnd becomes less than 1.5 at 1
    In addition we see W(wasted tokens) is negative, which shouldn't be as it contradicts assumptions and logic!
    output: 
    alpha =  1/10
    t  W              S              A              L              Ld_f_0         c_f_0          r_f_0          
0  -0.2875000000  0.0000000000   0.0062500000   0.0000000000   0.0000000000   3.9000000000   100.0000000000 
1  -0.2875000000  1.2875000000   4.0000000000   1.0062500000   0.0000000000   4.0000000000   100.0000000000 
2  -0.2875000000  1.2937500000   5.2875000000   1.0062500000   0.0000000000   4.0000000000   100.0000000000 
3  -0.2875000000  2.3937500000   5.2937500000   1.0062500000   0.0000000000   4.0000000000   100.0000000000 
4  -0.2875000000  3.2875000000   6.3937500000   1.0062500000   0.0000000000   4.0000000000   100.0000000000 
5  -0.2875000000  5.2875000000   6.3937500000   1.0062500000   0.0062500000   2.0000000000   100.0000000000 
6  -0.2875000000  6.2437500000   8.3937500000   1.0187500000   1.0062500000   2.1000000000   100.0000000000 
7  -0.2875000000  7.2875000000   9.3500000000   1.0250000000   1.0062500000   2.1000000000   100.0000000000 
8  -0.2875000000  7.2875000000   9.3562500000   1.0250000000   1.0187500000   1.0500000000   100.0000000000 
    '''

    c = ModelConfig.default()
    c.cca = "aimd"
    c.buf_min = 2
    c.buf_max = 2
    c.simplify = False
    #Behrooz: Increased time and specify enhancement to be false => original query and implementation
    c.T = 9
    c.enhancement=False
    s, v = make_solver(c)

    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    s.add(v.L[0] == 0)
    # Restrict alpha to small values, otherwise CCAC can output obvious and
    # uninteresting behavior
    s.add(v.alpha <= 0.1 * c.C * c.R)

    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    for t in range(2, c.T - 1):
        conds.append(
            And(
                v.c_f[0][t] <= 2,
                v.Ld_f[0][t + 1] - v.Ld_f[0][t] >=
                1,  # Burst due to loss detection
                v.S[t + 1 - c.R] - v.S[t - c.R] >=
                c.C + 1,  # Burst of BDP acks
                v.A[t + 1] >=
                v.A[t] + 2,  # Sum of the two bursts
                v.L[t+1] > v.L[t]
            ))

    # We don't want an example with timeouts
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

    s.add(Or(*conds))

    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c, qres.v)



def aimd_premature_loss_enhanced(timeout=60):
    '''
    This version forces query to ask about conditions in which cwnd
    becomes less than 2.
    At t=5 we observe the query condition is satisfied (cwnd=2)
    Then at T=9 we see cwnd drops below 1.5
output:
alpha =  1/10

t  W              S              A              L              Ld_f_0         c_f_0          r_f_0
0  0.0000000000   0.0000000000   0.0083333333   0.0000000000   0.0000000000   8.0000000000   100.0000000000
1  0.0000000000   1.0000000000   8.0000000000   6.0000000000   0.0000000000   8.0000000000   100.0000000000
2  0.0000000000   1.9916666667   8.0000000000   6.0000000000   3.0000000000   4.0000000000   100.0000000000
3  0.0000000000   2.3000000000   11.9916666667  7.2000000000   6.0000000000   4.0000000000   100.0000000000
4  0.0000000000   3.0000000000   12.3000000000  7.2000000000   6.0000000000   4.0000000000   100.0000000000
5  0.0000000000   5.0000000000   12.3000000000  7.2000000000   6.2000000000   2.0000000000   100.0000000000
6  0.0000000000   5.0000000000   14.3000000000  7.3000000000   7.2000000000   2.1000000000   100.0000000000
7  0.0000000000   6.9166666667   14.3000000000  7.3000000000   7.2000000000   2.1000000000   100.0000000000
8  0.0000000000   7.0916666667   16.3083333333  7.3083333333   7.2916666667   2.1000000000   100.0000000000
9  0.0000000000   8.0000000000   16.3083333333  7.3083333333   7.3000000000   1.0500000000   100.0000000000

    '''
    c = ModelConfig.default()
    c.cca = "aimd"
    c.buf_min = 2
    c.buf_max = 2
    c.simplify = False

    #Behrooz: increased duration, added enhancement, modified query
    #increase time to 10
    c.T = 10
    #repeating default values
    c.R=1
    c.C=1
    c.D=1
    #model corrections:
    c.enhancement=True

    s, v = make_solver(c)

    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    s.add(v.L[0] == 0)
    # Restrict alpha to small values, otherwise CCAC can output obvious and
    # uninteresting behavior
    s.add(v.alpha <= 0.1 * c.C * c.R)
    #Behrooz: forcing three dup acks as it is a variable.
    s.add(v.dupacks == 3 * v.alpha)
    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    for t in range(2, c.T - 1):
        conds.append(
            And(
                #this happens at t=5
                v.c_f[0][t] <= 2,
                v.Ld_f[0][t + 1] - v.Ld_f[0][t] >=
                1,  # Burst due to loss detection
                v.S[t + 1 - c.R] - v.S[t - c.R] >=
                c.C + 1,  # Burst of BDP acks
                v.A[t + 1] >=
                v.A[t] + 2,  # Sum of the two bursts
                v.L[t+1] > v.L[t],
                # Behrooz: Added to force cwnd become less than 2 in one of the next steps because it is not always guaranteed.
                Or(*[
                    v.c_f[0][t + i] < 2
                    for i in range(1, c.T - t)
                ])
            ))

    # We don't want an example with timeouts
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

    s.add(Or(*conds))

    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    #Behrooz: Added some debugging info
    if str(qres.satisfiable) == "sat":
        # Export all constraints (the solver's SMT2 representation) to a file.
        with open("model_constraints.smt2", "w") as f:
            f.write(s.to_smt2())

        # Export the solution: the model assigning values to all variables.
        with open("model_solution.txt", "w") as f:
            # You can use sexpr() to get an SMT-LIB S-expression representation
            for var, val in qres.model.items():
                f.write(f"{var} = {val}\n")
        plot_model(qres.model, c, qres.v)


if __name__ == "__main__":
    #aimd_premature_loss() #This is the original query authors provided.
    aimd_premature_loss_enhanced() #This is enhanced model and query
    #aimd_steady_state()

    '''
    import sys

    funcs = {
        "aimd_premature_loss": aimd_premature_loss,
        "bbr_low_util": bbr_low_util,
        "copa_low_util": copa_low_util
    }
    usage = f"Usage: python3 example_queries.py <{'|'.join(funcs.keys())}>"

    if len(sys.argv) != 2:
        print("Expected exactly one command")
        print(usage)
        exit(1)
    cmd = sys.argv[1]
    if cmd in funcs:
        funcs[cmd]()
    else:
        print("Command not recognized")
        print(usage)
    '''