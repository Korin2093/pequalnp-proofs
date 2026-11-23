# Circuit bounds and permanent level spaces

[Русская версия](RESULTS.ru.md)

These are reproducible results for questions posted by the P vs NP project. The circuit lower bounds below use exhaustive programs. The linked Lean files specify which statements have also been formally checked. The project's upstream checker awards contributor credit separately.

| Desk question | Result |
| --- | --- |
| L-meta-523 | All 218 nested minimum circuits admit a strictly reducing lift. |
| L-meta-583 | The once-subdivided complete graph on four vertices needs exactly **15** binary monotone gates. |
| L-meta-585 | Two triangles sharing a vertex need exactly **5 OR gates**, even with arbitrarily many AND gates. |
| L-meta-595 | The seven-vertex theta graph with path lengths 1, 2 and 5 needs exactly **11 gates** over AND, OR and NOT. |

## L-meta-523

The graph consists of a 6-cycle with one new leaf on each of two adjacent vertices. A minimum circuit has 11 gates. Up to swapping operands and reordering independent gates, there are 518 minimum circuits. In 300 there are no nested ANDs. The other 218 each have a desk-admissible lift that strictly reduces the number of nested AND pairs and preserves the output on all 256 assignments. The negative result concerns the existence of a circuit for which every admissible lift fails.

[Coverage argument and reproduction instructions](research/523/README.md) · [C++ checker](research/523/check.cpp) · [Independent Python checker](research/523/live523_independent.py) · [All 218 circuits and their lifts](research/523/lifts.tsv) · [Lean lemmas for the boundary assignments and search budget](lean/PEqualNP/Research/FrontierCut523.lean)

## L-meta-583

Insert one new vertex into each edge of the complete graph on four vertices. Two independent programs exclude every AND/OR circuit of at most 14 binary gates, including circuits that share wires. Both use the 12 minimal accepting and 12 maximal rejecting assignments. The programs record 422,613 losing states across the bounds. A circuit with 15 gates follows directly. At each original vertex, use two OR gates on its three subdivision neighbors and AND their result with the vertex. Three final OR gates combine the four terms.

Run `python3 research/583/live583.py`, or compile `c++ -O2 -std=c++17 research/583/live583.cpp -o check583` and run `./check583`. The Python source explains the cut criterion, gate budget and simplification of degenerate gates.

[Python search](research/583/live583.py) · [C++ search](research/583/live583.cpp) · [15-gate circuit checked by Lean](lean/PEqualNP/Research/Upper583.lean)

## L-meta-585

Let `a` be the vertex common to both triangles and let `b,c` and `d,e` be the other two pairs. Five OR gates suffice in `(a AND (b OR c OR d OR e)) OR (b AND c) OR (d AND e)`.

For the lower bound, record each wire on the six minimal accepting and five maximal rejecting assignments. Close the available set under arbitrary conjunctions. For every possible next OR, take the union of two available signatures and close under conjunction again. This includes arbitrary fanout and unlimited AND gates. On the last OR, any remaining false-positive row that survives all positive-covering old wires must be rejected by both operands. Exhaustion through four OR gates returns false. A separate SAT encoding also returns UNSAT at four.

[Run the exhaustive Python check](research/585/closure585.py) · [Five-OR upper bound checked by Lean](lean/PEqualNP/Research/Upper585.lean)

## L-meta-595

The graph joins two vertices by three paths of lengths 1, 2 and 5. All seven inputs affect the edge predicate. One search excludes every circuit of at most ten AND, OR and NOT gates. A second search uses AND gates with free input and output inversions and excludes even ten binary gates in this stronger model. Both searches use all 128 assignments. Four vertex-centered stars give an explicit eleven-gate upper bound. To reproduce, compile each source with `c++ -O2 -std=c++17` and run its executable with the default bound.

[Model and completeness argument](research/595/partial595-notes.md) · [AND/OR/NOT search](research/595/live595.cpp) · [Independent free-inversion search](research/595/partial595.cpp)

## Two infinite families checked by Lean

- For a cycle on 2h vertices with a leaf attached to every alternate vertex, every AND/OR/NOT circuit for the edge predicate needs at least 4h−1 gates when h ≥ 4. This proves the lower bound in L-meta-519 for that family. [Proof](lean/PEqualNP/Research/LeafDecor519.lean)
- Let a complex matrix subspace be invariant under a doubly transitive group of row permutations. Suppose the permanent of the all-ones matrix plus any member of the subspace equals n!. Every nonzero such subspace consists exactly of the matrices supported on one fixed column with zero column sum. Its dimension is n−1, and every such column space works. This resolves the row-symmetric case of L-gct-086. [Classification and sharpness](lean/PEqualNP/Research/TwoTransitiveClassification.lean)

Build the formal results from the repository's `lean` directory with `lake build PEqualNP.Research.FrontierCut523 PEqualNP.Research.Upper583 PEqualNP.Research.Upper585 PEqualNP.Research.LeafDecor519 PEqualNP.Research.TwoTransitiveClassification`.
