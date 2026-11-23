# Exhaustive check of L-meta-523

The posted statement asks for an 11-gate monotone two-input circuit on eight inputs whose output wire is 18. The target is true exactly when the selected vertices contain an edge of the graph with edges 01, 12, 23, 34, 45, 05, 06 and 17. The circuit must contain an AND above another AND. Every eligible lift must either give a wrong output or preserve at least the original number of ordered nested AND pairs.

The search found 518 circuits up to permutation of independent gates and interchange of a gate's operands. Of these, 218 contain nested AND gates. Every one of the 218 admits a lift with the same truth table and strictly fewer nested pairs. This is a standalone finite computational refutation of the posted existence claim. The C++ verifier does not produce a Lean kernel proof.

## Reproduce

A C++17 compiler and the standard library suffice. From this directory run

```sh
c++ -O2 -std=c++17 -Wall -Wextra -pedantic check.cpp -o check523
./check523
```

To emit one flattening lift per nested circuit, run `./check523 regenerated.tsv`. The reference file `lifts.tsv` contains the 218 gate lists, the zero-based gate index to edit, the original operand wire IDs p and h, and both nested-pair counts. Gates are listed in topological order and their output wires start at 8.

The expected output is recorded in `run.txt`. The verifier derives the boundary assignments from the graph, rebuilds the search, and verifies each completed trace against all 256 input assignments. The circuit descriptions and counts are obtained by running the search.

## Why the search covers every candidate

1. The target is monotone. Its minimal accepting assignments are the eight edges. The maximal rejecting assignments are the seven maximal independent sets. The checker derives both sets by testing all 256 assignments. Agreement there determines a monotone function on the whole cube. Each live wire has a 15-bit signature recording its value on the fifteen boundary assignments.
2. Consider a pair consisting of a minimal accepting assignment and a maximal rejecting assignment. At every cut, at least one remaining wire must be true on the former and false on the latter. Otherwise the vector presented to the remaining gates is coordinatewise below that on the rejecting assignment, and monotonicity makes the required outputs impossible. There are 56 such pairs. The only semantic pruning in the search checks whether some pair loses all its separating wires.
3. Every input of this graph is essential, as the checker verifies directly. In a circuit of minimum size all gates contribute to the output. A dead gate can be removed and later references renumbered. A gate with a repeated input wire computes that wire and can be bypassed and removed. These two observations permit restricting a minimum-size search to live gates with two different physical input wires. The search allows distinct physical wires to have equal signatures. Every predecessor index is valid by construction. The posted statement itself excludes forward references.
4. Trace a minimum circuit in its listed topological order. Initially the eight input wires are live. At a gate select its two input wires, produce the new wire, and consume either operand exactly on its last read. Keeping a selected operand live spends one unit. There is one live wire at the end, the output. For initial live count eight and gate count m the total number of units spent is m−7. Conversely, every such sequence is a valid straight-line monotone circuit. The two literal operand orders give the same computation and the same set of eligible lifts, since the verifier tries both choices of lifted operand.
5. The first search uses a budget of three units and allows unused budget on success. It finds no circuit with at most ten gates. Consequently every eligible 11-gate circuit is of minimum size and satisfies the structural properties above. The second search uses four units. For the yes/no lookahead, a sorted multiset of signatures plus remaining budget determines which continuations can succeed. It retains multiplicities and uses exact key comparison. For the enumeration, separate physical wire IDs are carried through the search. All successful choices are expanded, including distinct choices with the same continuation state.
6. Every completed trace is evaluated on all 256 assignments. For reporting and reusing lift checks, each gate receives an expression name formed by sorting the two child names and retaining the operator. All input labels are preserved. The checker verifies that there are no duplicate gate expressions and that every nonoutput wire is read. Therefore the output expression recovers the entire DAG by identifying its identical subexpressions. Traces with the same key differ only by topological numbering and swapping operands. Both preserve the queried reachability and lifts. The minimum-size check also independently excludes duplicate-expression gates.
7. For each circuit containing nested AND gates, the checker tries each nonoutput OR and each of its two operands as h. It tests h ≤ F on all 256 inputs, rewrites the OR to OR(p,p), appends OR(18,h), and evaluates the new output wire 19 on the whole cube. Each gate stores the set of AND ancestors inherited from its operands. For each AND gate the size of its inherited set contributes exactly once for each strict ancestor-AND pair. Traversing in gate order counts all ordered pairs in the statement, including pairs in parts disconnected by the lift. The checker accepts a flattening lift only if the output still equals F and the count strictly decreases.

## Results

| Quantity | Count |
| --- | ---: |
| Successful topological traces, treating each gate's operands as unordered | 2,409,150 |
| Flat formulas | 300 |
| Flat circuits with a shared internal gate | 0 |
| Nested formulas | 186 |
| Nested circuits with a shared internal gate | 32 |
| Nested circuits for which every admissible lift fails to flatten | 0 |

The labels 0 through 7 retain their identities. A shared gate is an internal gate read by more than one later gate. None of the 518 circuits has more than one shared internal gate.
