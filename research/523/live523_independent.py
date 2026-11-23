"""Independently enumerate all monotone AND/OR circuits for the L-meta-523 graph up to eleven gates.

On 8 positive edge assignments and 7 maximal independent sets, a live wire
covers a pair if its value is 1 on the edge and 0 on the independent set.
At every cut, every pair must have a live covering wire, by monotonicity.
A minimum circuit has no unused gates and reads every essential input.
After starting with 8 wires, every gate adds a wire and consumes 0, 1, or 2
wires on their last use. End with the output alone. Each retained operand
costs one unit beyond 7 gates. Try 0 through 4 units, to cover up to 11 gates.

The search omits a gate that repeats a live signal on the boundary or is
constant on all positives/all negatives: it can be bypassed or pinned, giving
a smaller circuit for the same function by monotonicity. This omission is sound
for finding minimum size and then enumerating every actual minimum circuit.
"""
from collections import Counter
from functools import cache
from itertools import combinations
import formula523 as check

positive,negative=check.EDGES,check.NEGATIVES
rows=positive+negative
target=(1<<len(positive))-1
input_sigs=tuple(sum(((x>>i)&1)<<j for j,x in enumerate(rows)) for i in range(8))
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
        for op,out in ((check.AND,a&b),(check.OR,a|b)):
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

@cache
def good(live,credit):
    return tuple(t for t in transitions(live,credit) if feasible(t[0],t[1]))

def normalized(gates):
    vals=list(range(8))
    counts=Counter()
    for op,a,b in gates:
        vals.append((op,*sorted((vals[a],vals[b]),key=repr)))
        counts[a]+=1;counts[b]+=1
    return vals[-1],sum(1 for i in range(8,8+len(gates)) if counts[i]>1)

@cache
def trace_count(live,credit):
    if len(live)==1:return int(live==(target,))
    return sum(trace_count(t[0],t[1]) for t in good(live,credit))

def verified_networks(start,credit):
    nodes=[None]*8
    signatures=list(input_sigs)
    index={}
    seen=set()
    results=set()
    def visit(live_ids,k):
        key=(live_ids,k)
        if key in seen:return
        seen.add(key)
        live=tuple(signatures[i] for i in live_ids)
        if len(live)==1:
            assert live==(target,)
            results.add(live_ids[0]);return
        ids=dict(zip(live,live_ids))
        for state,c,a,b,op,out in good(live,k):
            l,r=sorted((ids[a],ids[b]))
            triple=(op,l,r)
            if triple not in index:
                index[triple]=len(nodes);nodes.append(triple);signatures.append(out)
            v=index[triple]
            visit(tuple(v if s==out else ids[s] for s in state),c)
    visit(tuple(sorted(range(8),key=lambda i:signatures[i])),credit)
    for root in results:
        cache_id={}
        gs=[]
        def emit(i):
            if i<8:return i
            if i in cache_id:return cache_id[i]
            op,l,r=nodes[i];l,r=emit(l),emit(r)
            gs.append((op,l,r))
            cache_id[i]=len(gs)+7
            return cache_id[i]
        emit(root)
        assert len(gs)==11
        yield gs

if __name__=='__main__':
    start=tuple(sorted(input_sigs))
    for k in range(5):
        possible=feasible(start,k)
        print('at most',7+k,'gates',possible,flush=True)
        if possible:break
    table={}
    for gs in verified_networks(start,k):
        norm,shared=normalized(gs)
        key=(norm,bool(shared))
        if key not in table:table[key]=(shared,check.classify(gs))
    print('ordered gate traces',trace_count(start,k),'canonical formulas/DAGs',len(table),flush=True)
    print(Counter(table.values()),flush=True)
    forms=check.formulas(check.POS_MASK,check.NEG_MASK)
    missing=set(forms)-{f for (f,shared) in table if not shared}
    print('known minimum formulas missing from the enumeration',len(missing))
