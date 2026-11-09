import itertools,json,sys,collections
D=sys.argv[1]; comp={'A':'T','T':'A','C':'G','G':'C'}
rc=lambda w:''.join(comp[c] for c in reversed(w))
S=set(open(D+'/outputs/ssa5-best-set.txt').read().split())
w=lambda x,L:sum(c in L for c in x)
orient={L:sum(w(x,L)>=3 for x in S) for L in ['TC','AG','AC','TG','AT','CG']}
L=max(orient,key=orient.get)
dev=sorted(x for x in S if w(x,L)<3)
out=dict(dominance_alignment=orient,best_alignment=L,words_in_S_not_dominant=dev,count=len(dev),
 replaced_dominant_words=sorted(rc(x) for x in dev),
 patterns=collections.Counter(''.join('1' if c in L else '0' for c in x) for x in dev))
json.dump(out,open(D+'/outputs/ssa5-structure.json','w'),indent=1); print(json.dumps(out,indent=1))
