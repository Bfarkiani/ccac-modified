# Formally Verifying Congestion Control Performance

This repository analyzes the code accompanying the SIGCOMM 2021 paper _"Formally Verifying Congestion Control Performance"_ by Venkat Arun, Mina Tahmasbi Arashloo, Ahmed Saeed, Mohammad Alizadeh, and Hari Balakrishnan.

I examined the implementation in detail and discovered several caveats not discussed in the paper. To better understand these details, I prepared a comprehensive report, included in this repository.

My contributions include:

1. A complete analysis of the SMT-based implementation and its behavior.
2. Fixes to issues in the model, such as the presence of negative wasted tokens.
3. A demonstration that the AIMD steady-state bounds proposed in the paper do not always hold.

## Dependencies

- **Python** 3.8.5 or later  
- **Z3** SMT solver and its Python bindings  
  Install from: [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3)  
- **NumPy**, **SciPy**, **Matplotlib**

You can install the Python dependencies using:

```bash
pip install z3-solver numpy scipy matplotlib
