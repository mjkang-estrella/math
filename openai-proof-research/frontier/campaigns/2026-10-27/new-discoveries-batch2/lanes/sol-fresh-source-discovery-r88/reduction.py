import pathlib,json,random,math,hashlib,gzip,re
from fractions import Fraction as F
exec((pathlib.Path(__file__).parent/'check.py').read_text().split('counts={};')[0])
def coeff(m,n,c):
 out=[1]
 for z,s in [(1,j) for j in range(1,n+1)]+[(m,m*(n+c)-j) for j in range(n)]:
  new=[0]*(len(out)+1)
  for i,v in enumerate(out):new[i]+=s*v;new[i+1]+=z*v
  out=new
 return out
rng=random.Random(88);ident=0;minors=0;bad=[]
for m in [2,3,7,11,30]:
 for c,f in [(0,b),(1,a)]:
  for n in range(21):
   co=coeff(m,n,c)
   for k in [0,1,3,12,35]:
    v=sum(v*k**i for i,v in enumerate(co));den=math.factorial(n)*math.factorial(n+c)
    assert F(v,den)==f(m,n+k,k);ident+=1
  for t in range(80):
   r=2+t%7;rows=sorted(rng.sample(range(36),r));cols=sorted(rng.sample(range(36),r))
   d=det([[f(m,n+k,k) for k in cols] for n in rows]);minors+=1
   if d<=0:bad.append([m,c,rows,cols,str(d)])
print(json.dumps({'square_collocation_identities':ident,'sparse_square_minors':minors,'orders':'2..8','indices':'0..35','parameters':[2,3,7,11,30],'failures':bad},indent=2))
(L/'reduction-results.json').write_text(json.dumps({'identities':ident,'minors':minors,'failures':bad},indent=2))
# Exact published baseline rather than older raw-cache inventory.
freeze=L.parent/'root-edge-irregulator-final-freeze-r1';out={}
for name in ['omega','openai']:
 p=freeze/(name+'-tree.txt.gz');raw=p.read_bytes();lines=gzip.decompress(raw).decode().splitlines()
 out[name]={'compressed_sha256':hashlib.sha256(raw).hexdigest(),'entries':len(lines),'hits':[s for s in lines if re.search('narayana|fuss|amazing|signless.*spread|spread.*signless',s,re.I)]}
d=json.loads((L/'sources/omega-corrected-delta.json').read_text());out['delta']={'base':'6f8ee6614e0faf9dfa2cce46d1eb758dea97c335','head':json.loads((L/'heads.json').read_text())['omega'],'total_commits':d.get('total_commits'),'returned_commits':len(d.get('commits',[])),'returned_files':len(d.get('files',[])),'file_cap':300,'commit_cap':250,'matching_files':[f for f in d.get('files',[]) if re.search('narayana|fuss|amazing|signless.*spread|spread.*signless',f['filename'],re.I)]}
(L/'registry-audit.json').write_text(json.dumps(out,indent=2));print('delta',out['delta'])
