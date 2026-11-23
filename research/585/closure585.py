"""Independent exhaustive OR-cost verifier for the two triangles with a shared vertex."""
from functools import cache
from itertools import combinations

EDGES=((0,1),(0,2),(1,2),(0,3),(0,4),(3,4))
def f(x): return any((x>>i)&(x>>j)&1 for i,j in EDGES)
pos=tuple((1<<i)|(1<<j) for i,j in EDGES)
neg=tuple(x for x in range(32) if not f(x) and all(f(x|(1<<i)) for i in range(5) if not x>>i&1))
rows=pos+neg
P=(1<<len(pos))-1
full=(1<<len(rows))-1
wires=[sum(((x>>i)&1)<<j for j,x in enumerate(rows)) for i in range(5)]
def add(closure,new):
    return frozenset(closure|{v&new for v in closure})
d=frozenset({0,full})
for w in wires:d=add(d,w)
@cache
def search(D,k):
    if P in D:return True
    if k==0:return False
    # At the last OR, it must accept every positive and reject each negative
    # still accepted by all such earlier wires. ANDs after this OR are free.
    need=full
    for v in D:
        if v&P==P:need&=v
    if k==1:
        eligible=[v for v in D if not v&(need^P)]
        return any((a|b)&P==P for a,b in combinations(eligible,2))
    choices={a|b for a,b in combinations(D,2)}-D
    return any(search(add(D,v),k-1) for v in choices)
for k in range(5):print(k,search(d,k),search.cache_info(),flush=True)
print('Five ORs suffice: (a AND (b OR c OR d OR e)) OR (b AND c) OR (d AND e).')
