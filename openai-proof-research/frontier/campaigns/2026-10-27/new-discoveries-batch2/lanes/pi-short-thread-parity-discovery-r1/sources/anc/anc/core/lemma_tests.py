"""Computational sanity checks of the gluing lemma and the twin-branch lemma."""
import random, networkx as nx, decomp
random.seed(7)
def G(T):
    T=nx.convert_node_labels_to_integers(T)
    return decomp.grundy_original_tree(T.number_of_nodes(), list(T.edges()))
def m(T):
    d=dict(T.degree()); return sum(1 for u,v in T.edges() if d[u]>1 and d[v]>1)
def special(T):
    d=dict(T.degree()); return [v for v in T if d[v]>1 and any(d[u]==1 for u in T[v])]
bad=0
# gluing
for t in range(300):
    n1=random.randint(3,11); n2=random.randint(3,11)
    T1=nx.random_labeled_tree(n1,seed=random.randrange(10**9)); T2=nx.random_labeled_tree(n2,seed=random.randrange(10**9))
    w1=random.choice(special(T1)); w2=random.choice(special(T2))
    T2=nx.relabel_nodes(T2,{v:('b',v) for v in T2}); w2=('b',w2)
    U=nx.union(T1,T2); U=nx.contracted_nodes(U,w1,w2,self_loops=False)
    if G(U)!=G(T1)^G(T2) or m(U)!=m(T1)+m(T2): bad+=1; print("glue fail")
print("gluing tests done, failures:",bad)
# twin branches
bad=0
for t in range(300):
    nb=random.randint(1,6); nr=random.randint(1,9)
    B=nx.random_labeled_tree(nb,seed=random.randrange(10**9)) if nb>1 else nx.empty_graph(1)
    rb=random.choice(list(B.nodes()))
    R=nx.random_labeled_tree(nr,seed=random.randrange(10**9)) if nr>1 else nx.empty_graph(1)
    c=random.choice(list(R.nodes()))
    T=nx.Graph(R); T.add_nodes_from(R.nodes())
    for tag in ('x','y'):
        Bc=nx.relabel_nodes(B,{v:(tag,v) for v in B}); T=nx.union(T,Bc) if Bc.number_of_nodes() else T
        if Bc.number_of_edges()==0: T.add_node((tag,rb))
        T.add_edge(c,(tag,rb))
    if T.number_of_nodes()<3: continue
    # T': delete twins, attach a pendant leaf at c
    Tp=nx.Graph(R); Tp.add_nodes_from(R.nodes()); Tp.add_edge(c,'leaf')
    if G(T)!=G(Tp) or (m(T)-m(Tp))%2!=0: bad+=1; print("twin fail",list(T.edges()),G(T),G(Tp),m(T),m(Tp))
print("twin tests done, failures:",bad)
