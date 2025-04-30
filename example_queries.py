from z3 import And, Not, Or

from config import ModelConfig
from model import make_solver, min_send_quantum
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
    #c.simplify = False
    #c.enhancement=False
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
    Behrooz: As we see timing here does not match paper timing. 
    The burst of packets happen at t=6 but paper says it happens at t=7. Also we see w is negative.
 alpha =  1/10
Flow 0 timed out at:  []

 ============================== 

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
    #Behrooz: Increased time from 4 to 9
    # and specified enhancement to be false => original query and implementation
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
    c.T = 9
    #repeating default values
    c.R=1
    c.C=1
    c.D=1
    c.compose=True
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

def aimd_steady_state(timeout=60):
    '''
    This is the original steady state boundary check that authors used. it is originally used with
    T=10. The authors checked if query returns sat at T=10 and it returns unsat, and they
    concluded the steady state bounds hold.
    However, if you change exit condition check to be satisfied at any 2<=t, you see it return sat
alpha =  73333333333333327/240000000000000000
Flow 0 timed out at:  [6, 9]

 ==============================

t  W              S              A              L              Ld_f_0         c_f_0          r_f_0
0  -1.0000000000  0.0000000000   2.0277777778   0.0277777778   0.0000000000   3.0277777778   100.0000000000
1  -1.0000000000  1.9722222222   3.3333333333   1.3333333333   0.0000000000   3.3333333333   100.0000000000
2  -1.0000000000  2.7222222222   5.3055555556   1.3333333333   0.0000000000   3.3333333333   100.0000000000
3  -1.0000000000  3.0000000000   6.0555555556   1.3611111111   0.0000000000   3.3333333333   100.0000000000
4  -0.6944444444  4.6666666667   6.0555555556   1.3611111111   1.3333333333   1.6666666667   100.0000000000
5  -0.6944444444  5.6944444444   7.9722222222   2.2777777778   1.3333333333   1.9722222222   100.0000000000
6  0.0000000000   5.7222222222   8.2777777778   2.2777777778   2.2777777778   0.3055555556   100.0000000000
7  0.9722222222   6.0000000000   8.3055555556   2.2777777778   2.2777777778   0.3055555556   100.0000000000
8  1.6944444444   6.3055555556   8.5833333333   2.2777777778   2.2777777778   0.3055555556   100.0000000000
9  1.6944444444   6.3055555556   8.8888888889   2.2777777778   2.2777777778   0.3055555556   100.0000000000

Also as we see timeout happens! We can now use T=4 and use original exit condition.
    '''
    from model import Variables
    def max_cwnd(v: Variables):
        return c.C*(c.R + c.D) + c.buf_min + v.alpha

    def max_undet(v: Variables):
        return c.C*(c.R + c.D) + v.alpha

    c = ModelConfig.default()
    c.buf_min = 1
    c.buf_max = 1
    c.cca = "aimd"
    #Behrooz: shutting down enhancements
    c.enhancement =False
    c.T = 10
    s, v = make_solver(c)
    # Lemma's assumption
    s.add(v.L_f[0][0] - v.Ld_f[0][0] <= max_undet(v))
    s.add(v.c_f[0][0] <= max_cwnd(v))
    s.add(v.alpha < 1 / 3)
    # Lemma's statement's converse
    #original exit condition
    #s.add(Or(
    #    v.L_f[0][-1] - v.Ld_f[0][-1] > max_undet(v),
    #    v.c_f[0][-1] > max_cwnd(v)))
    #enhanced exit condition
    exit_conds = [v.c_f[0][t] > max_cwnd(v) for t in range(2, c.T)]
    s.add(Or(*exit_conds))


    print("Proving that if AIMD enters steady state, it will remain there")
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



def aimd_steady_state_enhanced(timeout=60):
    '''

```# With R=C=D=B=1 the enhanced model returns unsat. Are the steady state bounds valid?

    Testing with B=2, R=2, C=D=1:
alpha =  4583333333333333/15000000000000000
Flow 0 timed out at:  []

 ==============================

t  W              S              A              L              Ld_f_0         c_f_0          r_f_0
0  0.0000000000   0.0000000000   0.0277777778   0.0000000000   0.0000000000   5.0277777778   100.0000000000
1  0.0000000000   0.0000000000   6.1388888889   3.1388888889   0.0000000000   5.0277777778   100.0000000000
2  0.0000000000   1.1388888889   6.1388888889   3.1388888889   0.0000000000   5.0277777778   100.0000000000
3  0.0000000000   2.0000000000   6.1388888889   3.1388888889   0.0000000000   5.0277777778   100.0000000000
4  0.1388888889   3.0000000000   6.1666666667   3.1388888889   0.0000000000   5.0277777778   100.0000000000
5  1.1111111111   3.8611111111   7.0277777778   3.1388888889   0.0000000000   5.0277777778   100.0000000000
6  1.1111111111   3.8888888889   8.0277777778   3.1388888889   0.0000000000   5.0277777778   100.0000000000
7  1.2500000000   5.0277777778   8.8888888889   3.1388888889   0.0000000000   5.0277777778   100.0000000000
8  1.2500000000   5.7500000000   9.2222222222   3.1388888889   0.0000000000   5.3333333333   100.0000000000
9  1.2500000000   6.7500000000   10.8333333333  3.1388888889   3.1388888889   2.6666666667   100.0000000000

 So No they are not valid bounds.
    '''
    from model import Variables
    def max_cwnd(v: Variables):
        return c.C*(c.R + c.D) + c.buf_min + v.alpha

    def max_undet(v: Variables):
        return c.C*(c.R + c.D) + v.alpha
    c = ModelConfig.default()
    c.cca = "aimd"
    c.buf_min = 2
    c.buf_max = 2
    c.simplify = False

    #Behrooz: increased duration, added enhancement, modified query
    c.T = 10
    #repeating default values
    c.R=2
    c.C=1
    c.D=1
    c.compose=True
    #model corrections:
    c.enhancement=True

    s, v = make_solver(c)
    #behrooz: for this lemma, it is not necessary to set min_send_quantum as it is shown in file
    #aimd_proofs, but you can also set it
    #min_send_quantum(c, s, v)
    s.add(v.L[0] == 0)
    s.add(v.dupacks == 3 * v.alpha)
    s.add(v.alpha < 1 / 3)

    #original proof. only forces at 0
    s.add(v.L_f[0][0] - v.Ld_f[0][0] <= max_undet(v))
    s.add(v.c_f[0][0] <= max_cwnd(v))
    #Behrooz: I also force at t=1
    s.add(v.L_f[0][1] - v.Ld_f[0][1] <= max_undet(v))
    s.add(v.c_f[0][1] <= max_cwnd(v))

    #original exit
    #this is the same as below if we limit T to the time it exits.
    #exit_conds = v.c_f[0][-1] > max_cwnd
    #s.add(exit_conds)

    #checking can we exit at time >=2?
    exit_conds = [v.c_f[0][t] > max_cwnd(v) for t in range(2, c.T)]
    s.add(Or(*exit_conds))

    # We don't want an example with timeouts
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    if qres.satisfiable=='sat':
        print(f"max_cwnd={c.C*(c.R+c.D)+c.buf_min+qres.v.alpha}, max_undetected={c.C*(c.R+c.D)+qres.v.alpha}")

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

def bbr_low_util_enhanced(timeout=240):
    c = ModelConfig.default()
    c.compose = True
    c.cca = "bbr"
    # Simplification isn't necessary, but makes the output a bit easier to
    # understand
    #behrooz: enhancement and clarifications
    #unlimited buffer size
    c.simplify = False
    c.T=10
    c.enhancement=True
    c.C=1
    c.D=1
    c.R=1
    s, v = make_solver(c)
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

    # Consider the no loss case for simplicity
    s.add(v.L[0] == 0)
    # Ask for < 10% utilization. Can be made arbitrarily small
    s.add(v.S[-1] - v.S[0] < 0.1 * c.C * c.T)
    make_periodic(c, s, v, 2 * c.R)
    qres = run_query(c, s, v, timeout)
    print(qres.satisfiable)
    if str(qres.satisfiable) == "sat":
        plot_model(qres.model, c, qres.v)

if __name__ == "__main__":
    #aimd_premature_loss() #This is the original query authors provided.
    #aimd_premature_loss_enhanced() #This is enhanced model and query
    #aimd_steady_state() #This is original steady state check with modified exit
    #aimd_steady_state_enhanced() # This is enhanced model steady state check
    #bbr_low_util() #original bbr query
    bbr_low_util_enhanced() #enhanced bbr query

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