import pathlib,json,collections
D=pathlib.Path(__file__).resolve().parents[1]
A=[0,3,5,8,10,11,12,15,18,23,26,30,66,68,71,74,78,79,130,131,132,135,137,138,140,142,143,150,158,194,198,203,206,217]
# Independent coordinate comparison, deliberately not xor/popcount used in discovery.
def d(x,y):return sum(((x//2**i)%2)!=((y//2**i)%2) for i in range(8))
assert len(set(A))==34 and all(0<=x<256 for x in A)
assert max(d(x,y) for x in A for y in A)==5
rows=[]
for x in range(256):
 ds=[d(x,y) for y in A];mx=max(ds);w=A[ds.index(mx)]
 assert mx==5 if x in A else mx>5
 rows.append({'x':x,'in_A':x in A,'farthest_distance':mx,'farthest_witness':w})
cert={'A':A,'diameter':5,'cardinality':34,'ordered_pair_distance_histogram':dict(sorted(collections.Counter(d(x,y) for x in A for y in A).items())),'rows':rows}
(D/'certificate.json').write_text(json.dumps(cert,indent=2)+'\n');print(json.dumps(cert,indent=2))
