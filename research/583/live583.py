"""Exhaustive reproducible size calculation for L-meta-583 (Python 3.10+).

The 12 positive test points are the graph's edges, with only their endpoints
set. The 12 negative test points are its maximal independent sets. Agreement
there implies agreement on all 1024 inputs, since both circuit and target are
monotone. A wire separates a positive-negative pair when it is true at the
positive point and false at the negative one. At any computation cut, there
must be a live separator for every pair: if every available bit at the positive
point were <= its negative-point value, monotone downstream gates could never
reverse that relation.

Start with all 10 inputs live. Every input is relevant. In a smallest circuit,
there are no dead gates, constants, unary gates, duplicate operands, or invalid
wire reads: simplify them using the Boolean identities with 0/1 and propagate
aliases. At each binary gate, operands can be forgotten on last use, or kept
for future use. Ending at the single output, a circuit with g gates keeps
exactly g-(10-1) operand occurrences. Thus a budget of 5 enumerates circuits
through size 14. The minimum cannot have a gate equal on the test points to
another live wire: redirect its uses there and save one gate. Likewise, a
gate false on every positive point can be pinned false, which preserves the
positives and can only lower negatives; symmetrically pin true when true at
all negative points. The function is nonconstant, so these simplifications
never incur a new constant output gate. The remaining gates have two distinct
inputs. Each recursive step consumes one unit of len(live)+remaining_budget,
and only genuinely equivalent cut states are memoized.

Usage: python live583.py
"""
from functools import cache
from itertools import combinations

import itertools
pairs=tuple(itertools.combinations(range(4),2))
positive=tuple((1<<i)|(1<<(4+j)) for j,p in enumerate(pairs) for i in p)
f=lambda x:any(x&e==e for e in positive)
negative=tuple(x for x in range(1024) if not f(x) and all(f(x|(1<<i)) for i in range(10) if not x>>i&1))
rows=positive+negative
target=(1<<len(positive))-1
input_sigs=tuple(sum(((x>>i)&1)<<j for j,x in enumerate(rows)) for i in range(10))
all_pairs=(1<<(len(positive)*len(negative)))-1

@cache
def cover(v):
    return sum(1<<(p*len(negative)+n)
        for p in range(len(positive)) if (v>>p)&1
        for n in range(len(negative)) if not (v>>(len(positive)+n))&1)

def transitions(live,credit):
    for i,j in combinations(range(len(live)),2):
        a,b=live[i],live[j]
        other=tuple(v for pos,v in enumerate(live) if pos not in (i,j))
        rest_cov=0
        for v in other: rest_cov|=cover(v)
        for op,out in ((0,a&b),(1,a|b)):
            if out in live or not cover(out):continue
            for kept in ((),(a,),(b,),(a,b)):
                if len(kept)>credit:continue
                cov=rest_cov|cover(out)
                for k in kept:cov|=cover(k)
                if cov!=all_pairs:continue
                next_live=tuple(sorted(other+kept+(out,)))
                yield next_live,credit-len(kept),a,b,op,out

@cache
def feasible(live,credit):
    if len(live)==1:return live==(target,)
    return any(feasible(state,k) for state,k,*_ in transitions(live,credit))

start=tuple(sorted(input_sigs))
print("boundaries",len(positive),len(negative),flush=True)
for excess in range(6):
    result=feasible(start,excess)
    print("at most",9+excess,"gates",result,feasible.cache_info(),flush=True)
    if result: break

# The matching construction is independently tested on every Boolean input.
terms=[[4,5,6],[4,7,8],[5,7,9],[6,8,9]]
def size15(x):
    return any((x >> i & 1) and any(x >> j & 1 for j in row)
               for i,row in enumerate(terms))
assert all(bool(size15(x)) == f(x) for x in range(1<<10))
print("15 gates suffice: four 3-input neighbor ORs, four ANDs, three ORs")
