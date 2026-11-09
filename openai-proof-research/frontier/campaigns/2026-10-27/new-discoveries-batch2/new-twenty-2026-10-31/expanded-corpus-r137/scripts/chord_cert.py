# Certificate for the 5-chord base lemma (329080), over all 945 standard labelled words with 5 chords.
# P(w): (some chord crosses no other chord) and (for every triangle {a,b,c} of pairwise crossing chords,
#        the two remaining chords x,y each have cyclically adjacent endpoints, and all four of their
#        endpoints lie in one arc between consecutive endpoints of a,b,c).
# For every w with not P(w) we record a side mask with exactly one face in the 2n-dart model
# (genus (2+5-1)/2 = 3), so max genus(w) >= 3.  Also: R3 = 123123 has no configuration with 5 faces.
import sys,json,itertools,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from chord_dart import dart_faces,words
def pos(w,a): return [i for i,c in enumerate(w) if c==a]
def crosses(w,a,b):
    pa=pos(w,a);pb=pos(w,b); return (pa[0]<pb[0]<pa[1])!=(pa[0]<pb[1]<pa[1])
def P(w):
    n=len(w)//2;L=len(w)
    iso=any(all(not crosses(w,a,b) for b in range(n) if b!=a) for a in range(n))
    if not iso: return False
    for t in itertools.combinations(range(n),3):
        if all(crosses(w,x,y) for x,y in itertools.combinations(t,2)):
            tp=sorted(i for a in t for i in pos(w,a))
            others=[x for x in range(n) if x not in t]
            arcs=set()
            for x in others:
                p=pos(w,x)
                if not ((p[1]-p[0])==1 or (p[0]==0 and p[1]==L-1)): return False
                # arc index: number of triangle endpoints before p[0] (mod 6), cyclic arcs
                k=[sum(1 for q in tp if q<pp)%6 for pp in p]
                if k[0]!=k[1]: return False
                arcs.add(k[0])
            if len(arcs)!=1: return False
    return True
cert=[];good=0
for w in words(5):
    if P(w): good+=1; continue
    for m in range(1<<10):
        if dart_faces(w,m)==1: cert.append({'word':list(w),'mask':m}); break
    else: raise SystemExit('NO WITNESS for '+str(w))
r3=[m for m in range(1<<6) if dart_faces((0,1,2,0,1,2),m)==5]
# arc-index note: cyclic arc k (k=0..5) is the arc after the k-th triangle endpoint; arc 0 wraps around.
out={'words_total':good+len(cert),'P_holds':good,'witnessed_genus3':len(cert),'R3_configs_with_5_faces':len(r3),'certificate':cert}
pathlib.Path(sys.argv[1]).write_text(json.dumps(out)+'\n')
print({k:v for k,v in out.items() if k!='certificate'})
