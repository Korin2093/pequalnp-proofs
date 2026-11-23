"""Exhaust the minimum AND/OR formula trees for pequalnp.com step L-meta-523.

Run with Python 3.10 or later: python formula523.py
No external packages, input files, or network access are required.

For positive graph-edge assignments P and negative maximal independent sets N,
a leaf labelled k separates P from N iff coordinate k is 1 on all of P and 0
on all of N. At an OR the positive assignments can be partitioned between
the children, each of which rejects every negative assignment. At an AND,
partition the negative assignments, and require each child to accept all
positives. In a minimum formula both parts are nonempty: otherwise one child
already separates everything. This gives the exact minimum leaf count and,
by following every optimal split, all minimum trees. Child permutations and
multiple valid routings of the same labeled tree are deduplicated.

A monotone formula separating the full two sets computes the specified graph
function. Its 256 values and the values of every proposed successful lift
are independently checked below. A finite check on formula trees does not
exclude general circuits with shared internal wires.
"""
from collections import Counter
from functools import cache
from itertools import product

EDGE_VERTICES = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5), (0, 6), (1, 7))
EDGES = tuple((1 << i) | (1 << j) for i, j in EDGE_VERTICES)
N_VARS = 8


def function_value(assignment):
    return any(assignment & edge == edge for edge in EDGES)


NEGATIVES = tuple(
    assignment for assignment in range(2**N_VARS)
    if not function_value(assignment) and all(
        function_value(assignment | (1 << i))
        for i in range(N_VARS) if not assignment & (1 << i)
    )
)
POS_MASK = (1 << len(EDGES)) - 1
NEG_MASK = (1 << len(NEGATIVES)) - 1
INPUT_COLUMNS = tuple(sum(((x >> i) & 1) << x for x in range(256)) for i in range(N_VARS))
TARGET = sum(int(function_value(x)) << x for x in range(256))
AND, OR = 0, 1


@cache
def unordered_splits(mask):
    """All nontrivial bipartitions; first part contains the least set bit."""
    result = []
    part = (mask - 1) & mask
    while part:
        if part & (mask & -mask):
            result.append((part, mask ^ part))
        part = (part - 1) & mask
    return tuple(result)


@cache
def leaf_labels(pos, neg):
    return tuple(
        k for k in range(N_VARS)
        if all(x & (1 << k) for j, x in enumerate(EDGES) if pos & (1 << j))
        and all(not x & (1 << k) for j, x in enumerate(NEGATIVES) if neg & (1 << j))
    )


def child_problems(pos, neg):
    for left, right in unordered_splits(pos):
        yield OR, (left, neg), (right, neg)
    for left, right in unordered_splits(neg):
        yield AND, (pos, left), (pos, right)


@cache
def leaf_count(pos, neg):
    if leaf_labels(pos, neg):
        return 1
    return min(leaf_count(*l) + leaf_count(*r) for _, l, r in child_problems(pos, neg))


def optimal_splits(pos, neg):
    size = leaf_count(pos, neg)
    for op, left, right in child_problems(pos, neg):
        if leaf_count(*left) + leaf_count(*right) == size:
            yield op, left, right


@cache
def formulas(pos, neg):
    if leaf_count(pos, neg) == 1:
        return frozenset(leaf_labels(pos, neg))
    result = set()
    for op, left, right in optimal_splits(pos, neg):
        for x, y in product(formulas(*left), formulas(*right)):
            result.add((op, *sorted((x, y), key=repr)))
    return frozenset(result)


def gate_list(tree):
    result = []

    def emit(node):
        if isinstance(node, int):
            return node
        op, left, right = node
        result.append((op, emit(left), emit(right)))
        return N_VARS + len(result) - 1

    emit(tree)
    return result


def wire_values(gates):
    wires = list(INPUT_COLUMNS)
    for op, left, right in gates:
        a, b = wires[left], wires[right]
        wires.append(a | b if op == OR else a & b)
    return wires


def nested_pairs(gates):
    """Count strict AND-to-AND ancestor pairs, once per ordered gate pair."""
    ancestors = [0] * N_VARS
    pairs = 0
    for j, (op, left, right) in enumerate(gates):
        below = ancestors[left] | ancestors[right]
        if op == AND:
            pairs += below.bit_count()
            below |= 1 << j
        ancestors.append(below)
    return pairs


def classify(gates):
    wires = wire_values(gates)
    assert len(gates) == 11 and wires[18] == TARGET
    count = nested_pairs(gates)
    if not count:
        return 'flat'
    for j, (op, left, right) in enumerate(gates[:-1]):
        if op != OR:
            continue
        for p, h in ((left, right), (right, left)):
            if wires[h] & ~TARGET:
                continue
            lifted = list(gates)
            lifted[j] = (OR, p, p)
            lifted.append((OR, 18, h))
            if wire_values(lifted)[19] == TARGET and nested_pairs(lifted) < count:
                return 'has a strictly reducing lift'
    return 'witness'


if __name__ == '__main__':
    cost = leaf_count(POS_MASK, NEG_MASK)
    trees = formulas(POS_MASK, NEG_MASK)
    counts = Counter(classify(gate_list(tree)) for tree in trees)
    print(f'{len(EDGES)} edge assignments, {len(NEGATIVES)} maximal independent sets')
    print(f'Minimum formula size: {cost} leaves, {cost-1} gates')
    print(f'{len(trees)} distinct minimum formulas up to gate-input swaps')
    for label in ('flat', 'has a strictly reducing lift', 'witness'):
        print(f'  {label}: {counts[label]}')
