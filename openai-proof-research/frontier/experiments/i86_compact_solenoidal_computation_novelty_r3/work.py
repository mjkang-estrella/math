import pathlib,json,hashlib,re,sys,collections
ROOT=pathlib.Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i86_compact_solenoidal_computation_novelty_r3'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,d): (S/n).write_text(json.dumps(d,indent=2)+'\n')
def get(n):return json.loads((S/n).read_text())
def ref(p):
 p=pathlib.Path(p);b=(ROOT/p).read_bytes();return {'path':str(p),'sha256':sha(b),'bytes':len(b)}
if sys.argv[1]=='setup':
 refs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','frontier/sources/i80_geometric_flows_computation_discovery/seal-v1.json','frontier/sources/i80_geometric_flows_computation_discovery/full-brief.txt','frontier/iterations/i80-geometric-flows-computation-discovery.md','frontier/experiments/i80-parent-verification.json']
 put('immutable-refs.json',[ref(p) for p in refs]);(S/'snapshots').mkdir(exist_ok=True)
 led=[]
 for p in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:
  dest=S/'snapshots'/p.replace('/','__');dest.write_bytes((ROOT/p).read_bytes());led.append({'live':p,'snapshot':str(dest.relative_to(ROOT)),**ref(p)})
 put('ledgers.json',led)
 d=json.loads((ROOT/refs[4]).read_text());put('search-domain.json',d)
 patterns={'fluid':r'Navier.Stokes|solenoidal|incompressible|Euler flow|fluid computation','compact-pressure':r'compact.{0,70}pressure|pressure.{0,70}compact|harmonic moment|radial swirl|Gavrilov|Grad.Shafranov|Brandolese|localizab','gates':r'rotation.{0,70}(gate|plateau|compact)|pressure.balanc|stationary Euler|Leray|Helmholtz|solenoidal.{0,50}(routing|forc)'}
 allhits={}
 for name,pat in patterns.items():
  reg=re.compile(pat,re.I);hits=[]
  for x in d:
   b=(ROOT/x['local']).read_bytes();assert sha(b)==x['sha256']
   for i,line in enumerate(b.decode('utf8','replace').splitlines(),1):
    if reg.search(line):hits.append([x['path'],i,line])
  put('search-'+name+'.json',hits);allhits[name]={'pattern':pat,'flags':'IGNORECASE','hits':len(hits),'files':len(set(x[0] for x in hits)),'manuscripts':dict(collections.Counter(x[0].split('/')[1] for x in hits))}
 put('searches.json',allhits)
 m=json.loads((ROOT/'frontier/sources/i80_geometric_flows_computation_discovery/source-manifest.json').read_text());m=[x for x in m if x['family'] in ['RV','ES','VD','SP','IB','GS','FS','PI','FP']];put('fluid-manifest.json',m)
 unique=[];seen={}
 for x in m:
  if x['sha256'] in seen:continue
  seen[x['sha256']]=x['path'];unique.append(x)
 put('read-queue.json',unique);put('reads.json',[])
 print('searches',allhits);print('unique files',len(unique),'lines',sum(len((ROOT/x['path']).read_text().splitlines()) for x in unique))
elif sys.argv[1]=='read':
 q=get('read-queue.json');x=q[int(sys.argv[2])];lines=(ROOT/x['path']).read_text().splitlines(keepends=True);start=int(sys.argv[3]) if len(sys.argv)>3 else 1;end=min(int(sys.argv[4]),len(lines)) if len(sys.argv)>4 else len(lines)
 print('FILE',sys.argv[2],x['family'],x['upstream_path'],len(lines),'LINES',start,end)
 print(''.join(f'{i}: {lines[i-1]}' for i in range(start,end+1)),end='')
 r=get('reads.json');r.append({'path':x['path'],'sha256':x['sha256'],'start':start,'end':end,'passage_sha256':sha(''.join(lines[start-1:end]).encode())});put('reads.json',r)
elif sys.argv[1]=='queue':
 for i,x in enumerate(get('read-queue.json')):print(i,x['family'],x['upstream_path'].split('/build/')[-1],len((ROOT/x['path']).read_text().splitlines()))
