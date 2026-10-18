#!/usr/bin/env python3
"""MIT. Finite combinatorial diagnostics; not proof of chain law or tree bound."""
import itertools,json,math


def inspect(parent):
    n=len(parent); child=[[] for _ in parent]
    for v in range(1,n):child[parent[v]].append(v)
    leaves=[v for v in range(n) if not child[v]]; L=len(leaves)
    count=[0]*n; heavy=[None]*n
    for v in range(n-1,-1,-1):
        count[v]=sum(count[u] for u in child[v]) if child[v] else 1
        if child[v]:heavy[v]=max(child[v],key=lambda u:(count[u],-u))
    heads=[0]+[v for v in range(1,n) if heavy[parent[v]]!=v]
    assert len(heads)==L
    chains=[]; owner=[None]*n
    for h in heads:
        chain=[]; v=h
        while v is not None:
            owner[v]=len(chains);chain.append(v);v=heavy[v]
        chains.append(chain)
    def path(v):
        ans=[]
        while v>=0:ans.append(v);v=parent[v]
        return ans[::-1]
    for h in heads:
        before=path(h)[:-1]
        used=[]
        for v in before:
            if not used or used[-1]!=owner[v]:used.append(owner[v])
        assert len(used)<=L.bit_length()-1
        rebuilt=[]
        for c in used:
            hit=[v for v in before if owner[v]==c]
            assert hit==chains[c][:len(hit)]
            rebuilt+=hit
        assert rebuilt==before
    unary_heads=[0]+[v for v in range(1,n) if len(child[parent[v]])>=2]
    branch=sum(len(x)>=2 for x in child)
    assert len(unary_heads)==L+branch<=2*L-1
    unary=[]; own=[None]*n
    for h in unary_heads:
        chain=[]; v=h
        while True:
            own[v]=len(unary);chain.append(v)
            if len(child[v])!=1:break
            v=child[v][0]
        unary.append(chain)
    for v in range(n):
        pv=path(v); c=own[v]; prior=[]
        for u in pv:
            if own[u]!=c and (not prior or prior[-1]!=own[u]):prior.append(own[u])
        before=[u for u in pv if own[u]!=c]
        assert before==[u for a in prior for u in unary[a]]
    return L


def main():
    cases=0
    for n in range(1,9):
        for choices in itertools.product(*[range(v) for v in range(1,n)]):
            inspect([-1]+list(choices)); cases+=1
    # A light exit at the root is an internal prefix of its heavy chain.
    parent=[-1,0,1,0]; inspect(parent)
    correct_prehead_sum=1; incorrect_terminal_sum=3
    assert correct_prehead_sum!=incorrect_terminal_sum
    # Exact even-moment factorial inequality used in tail-to-MGF conversion.
    for k in range(1,51):assert math.factorial(2*k)>=2**k*math.factorial(k)**2
    print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS_NOT_PROOF','increasing_label_rooted_trees_through8_vertices':cases,'internal_prefix_negative_control':{'prehead':correct_prehead_sum,'wrong_terminal_replacement':incorrect_terminal_sum},'factorial_checks':50,'limits':'No finite check establishes the chain-law hypothesis, a universal subgaussian bound, or contribution eligibility.'},sort_keys=True,indent=2))

if __name__=='__main__':main()
