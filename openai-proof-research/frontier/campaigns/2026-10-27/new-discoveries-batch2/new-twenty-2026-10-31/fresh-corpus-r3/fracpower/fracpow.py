# Search for graphs G (connected, Delta>=3, G != C3xK2) and 1<m<n with chi(G^{m/n}) > omega(G^{m/n}).
# G^{m/n}: m-th power of the n-subdivision of G. Exact clique number (networkx) and exact
# k-colourability via CaDiCaL on a direct CNF encoding.
import networkx as nx, itertools, subprocess, sys, json, os, tempfile
TLIM=int(os.environ.get('TLIM','60'))
CADICAL='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
def frac_power(G,m,n):
    S=nx.Graph(); S.add_nodes_from(('v',u) for u in G.nodes())
    for (u,v) in G.edges():
        path=[('v',u)]+[('e',min(u,v),max(u,v),i if u<v else n-i) for i in range(1,n)]+[('v',v)]
        # ensure consistent naming: internal vertex at distance i from min endpoint
        path=[('v',u)]+[('e',u,v,i) for i in range(1,n)]+[('v',v)]
        nx.add_path(S,path)
    P=nx.Graph(); P.add_nodes_from(S.nodes())
    for x,d in nx.all_pairs_shortest_path_length(S,cutoff=m):
        for y,l in d.items():
            if 0<l<=m: P.add_edge(x,y)
    return P
def colourable(P,k):
    idx={v:i for i,v in enumerate(P.nodes())}; N=len(idx); var=lambda v,c: idx[v]*k+c+1
    cl=[[var(v,c) for c in range(k)] for v in P.nodes()]
    for (u,v) in P.edges():
        for c in range(k): cl.append([-var(u,c),-var(v,c)])
    # symmetry breaking: a max clique gets fixed colours
    Q=max(nx.find_cliques(P),key=len)
    for c,v in enumerate(Q[:k]): cl.append([var(v,c)])
    with tempfile.NamedTemporaryFile('w',suffix='.cnf',delete=False) as f:
        f.write('p cnf %d %d\n'%(N*k,len(cl))); f.writelines(' '.join(map(str,c))+' 0\n' for c in cl); fn=f.name
    r=subprocess.run([CADICAL,'-q','-t',str(TLIM),fn],capture_output=True,text=True); os.unlink(fn)
    return {10:True,20:False}.get(r.returncode,None)
if __name__=='__main__':
    from networkx.generators.atlas import graph_atlas_g
    prism=nx.circular_ladder_graph(3)
    ms=[int(a) for a in sys.argv[1].split(',')]; nmax_extra=int(sys.argv[2])
    out=[]
    for gi,G in enumerate(graph_atlas_g()):
        if G.number_of_nodes()<4 or not nx.is_connected(G) or max(d for _,d in G.degree())<3: continue
        if G.number_of_edges()==G.number_of_nodes()*(G.number_of_nodes()-1)//2: continue  # complete graphs: proved in source section 6
        print("graph",gi,flush=True)
        for m in ms:
            for n in range(m+1,m+1+nmax_extra):
                P=frac_power(G,m,n); w=len(max(nx.find_cliques(P),key=len))
                ok=colourable(P,w)
                if ok is None:
                    und={'atlas':gi,'m':m,'n':n,'omega':w,'undecided_after_s':TLIM}; out.append(und); print('UNDECIDED',und,flush=True); continue
                if not ok:
                    iso=nx.is_isomorphic(G,prism)
                    rec={'atlas':gi,'nodes':G.number_of_nodes(),'edges':sorted(G.edges()),'m':m,'n':n,'omega':w,'prism':iso}
                    out.append(rec); print('CHI>OMEGA',rec,flush=True)
    json.dump(out,open('fracpow_%s_%d.json'%(sys.argv[1].replace(',','-'),nmax_extra),'w'),indent=1)
    print('done',len(out))
