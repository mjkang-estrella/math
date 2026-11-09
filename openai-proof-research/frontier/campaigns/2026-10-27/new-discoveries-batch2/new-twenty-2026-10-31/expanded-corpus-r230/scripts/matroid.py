import itertools,json
# Definition 10, r=4,t=4; relax C_4 union X; delete C_4.
r=4;t=4;C=[{2*i,2*i+1} for i in range(t)];X={8,9};H=[p|X for p in C]+[C[i]|C[i+1] for i in range(t-1)];relaxed=C[3]|X;H.remove(relaxed);E=set(range(6))|X
ret=[sorted(h) for h in H if h<=E];standard=[sorted(C[i]|X) for i in range(3)]+[sorted(C[i]|C[i+1]) for i in range(2)]
assert sorted(ret)==sorted(standard)
# Ranks under the sparse paving bases: every 4-set except retained hyperplanes.
B=[set(b) for b in itertools.combinations(E,4) if set(b) not in H]
def rank(S):return max(len(S&b) for b in B)
A=C[1];B0=X;CC=C[0];DD=C[2]
lhs=sum(rank(a|b) for a,b in [(A,B0),(A,CC),(A,DD),(B0,CC),(B0,DD)])
rhs=rank(A)+rank(B0)+rank(A|B0|CC)+rank(A|B0|DD)+rank(CC|DD)
print(json.dumps(dict(r=r,t=t,relaxed=sorted(relaxed),restriction=sorted(E),hyperplanes=ret,ingleton_lhs=lhs,ingleton_rhs=rhs,conclusion='15 < 16, nonrepresentable via classical Ingleton; routine source-definition bridge, zero discovery credit')),flush=True)
assert lhs<rhs
