from pathlib import Path,PurePosixPath
import json,hashlib,zipfile,stat,math,time,resource
L=Path(__file__).resolve().parents[1]
def h(b): return hashlib.sha256(b).hexdigest()
zpath=L/'schrijver-source-r5.zip'
assert h(zpath.read_bytes())=='685b78855d145dae95ba175796528739f8a9ee5ea54fb621fc78b5ccdc763d1b'
out=L/'proof-packet-safe'; out.mkdir(exist_ok=True)
with zipfile.ZipFile(zpath) as z:
 names=z.namelist(); assert len(names)==len(set(names)); hashes={}
 for info in z.infolist():
  p=PurePosixPath(info.filename)
  assert not p.is_absolute() and '..' not in p.parts and chr(92) not in info.filename
  assert not stat.S_ISLNK(info.external_attr>>16)
  assert p.suffix not in ['.olean','.ilean','.o','.so','.a']
  if info.is_dir(): continue
  b=z.read(info); dest=out.joinpath(*p.parts);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);hashes[info.filename]=h(b)
 manifest=json.loads(z.read('SOURCE-MANIFEST.json'))
 assert all(hashes[n]==v for n,v in manifest.items())
 modules=sum(n.startswith('src/') and n.endswith('.lean') for n in names); assert modules==474
(L/'safe-extraction.json').write_text(json.dumps({'pass':True,'modules':modules,'no_execution':True,'packet_sha256':h(zpath.read_bytes()),'manifest_entries_verified':len(manifest),'member_hashes':hashes},indent=2)+'\n')
def bits(x):
 while x:
  b=x&-x;yield b.bit_length()-1;x-=b
records=[]
for n,k in [(14,6),(27,12),(28,12),(29,13),(30,13)]:
 start=time.monotonic();d=json.loads((L/f'evidence/leads-review-r122/outputs/graph-{n}-{k}-certificate.json').read_text());v=d['vertices']; N=len(v); full=(1<<N)-1
 generated=[]
 def gen(pos,left,m):
  if not left:
   if not (m&1 and m&(1<<(n-1))): generated.append(m)
   return
  for a in range(pos,n-2*(left-1)):
   gen(a+2,left-1,m|(1<<a))
 gen(0,k,0);assert len(v)==len(set(v));assert set(v)==set(generated);assert N==n*math.comb(n-k,k)//(n-k)
 adjacency=[sum(1<<j for j,b in enumerate(v) if not a&b) for a in v];assert adjacency==d['adjacency']
 def check(root,layers):
  seen=0; frontier=1<<root
  for layer in layers:
   assert layer==frontier and not seen&layer;seen|=layer
   neigh=0
   for i in bits(layer): neigh|=adjacency[i]
   frontier=neigh&~seen&full
  assert seen==full and frontier==0
 check(d['source'],d['levels']); mask=(1<<n)-1;covered=set();maxdist=0
 for root,layers in d['representative_levels']:
  check(root,layers);maxdist=max(maxdist,len(layers)-1)
  for t in range(n): covered.add(((v[root]<<t)|(v[root]>>(n-t)))&mask)
 assert covered==set(v)
 assert maxdist=={14:5,27:8,28:6,29:9,30:7}[n]
 witness=d['witness'];assert len(witness)==2
 if n==27:
  assert v[d['source']]==21669205
  assert d['levels'][8] & (1<<v.index(39144021))
  path=json.loads((L/'evidence/distance-eight-path.json').read_text())['masks']
  assert len(path)==9 and path[0]==21669205 and path[-1]==39144021
  assert all(m in v for m in path) and all(not a&b for a,b in zip(path,path[1:]))
 if n==14:
  aa=sum(1<<(i-1) for i in [1,3,5,7,9,12]);bb=sum(1<<(i-1) for i in [1,3,6,8,10,12])
  def ball2(m):
   root=v.index(m);b=(1<<root)|adjacency[root]
   for j in bits(adjacency[root]):b|=adjacency[j]
   return b
  ba,bb2=ball2(aa),ball2(bb);assert ba.bit_count()==17 and bb2.bit_count()==13 and not ba&bb2

 records.append({'n':n,'k':k,'vertices':N,'diameter':maxdist,'rotation_roots':len(d['representative_levels']),'source_layer_sizes':[x.bit_count() for x in d['levels']],'witness_indices':witness,'seconds':time.monotonic()-start})
 print(records[-1],flush=True)
(L/'certificate-verification.json').write_text(json.dumps({'pass':True,'method':'own literal mask enumeration; all literal disjointness adjacencies; exact BFS recurrences; full rotation coverage','graphs':records,'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},indent=2)+'\n')
