EXACT VERIFICATION — A Counterexample to the Huneke–Wiegand Conjecture
Son Pham; manuscript dated 6 September 2026.

Requirements: Python 3.10 or later; standard library only. No external data,
network connection, third-party Python package, or repository checkout is needed.
The release checks were run with Python 3.13.5.

From the source-package root, run:
    python3 anc/verify_counterexample.py
    python3 anc/verify_tensor_graph.py

Each program prints deterministic JSON with status PASS and exits successfully
only after completing its checks. A failed check raises an exception and returns
a nonzero exit status. Checks remain enabled under python3 -O.

Compare the output with expected_arithmetic.json and expected_tensor_graph.json.
The arithmetic program uses exact Apéry residue minima to verify infinite
relative-ideal identities. The second program independently constructs semigroup
membership by dynamic programming and checks tensor-graph connectivity. The two
programs do not import one another.

For the main example, all 690 nonempty tensor graphs in degrees 56 through 783
are connected; the proof in Section 7 covers every degree at least 784. The graph
program additionally checks two examples with torsion and one principal ideal.

These programs verify the explicit integer certificates. The algebraic passages
from those certificates to rings, modules, duals, and completion are proved in
the manuscript. The computations are not a formal proof-assistant development.
