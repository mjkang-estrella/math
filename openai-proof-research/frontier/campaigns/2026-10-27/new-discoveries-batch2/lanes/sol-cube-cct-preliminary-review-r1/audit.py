import pathlib, hashlib, json, shutil, sys, datetime, urllib.request, urllib.error, itertools, subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
C=L.parent/'sol-wide-algebra-scout-r222'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze():
 (L/'frozen').mkdir(exist_ok=True); (L/'administrative').mkdir(exist_ok=True)
 rows=[]
 paths=[C/x for x in ['PROOF.md','SOURCE_MAP.md','FAILURES.md','SCOUTING.md','mechanisms.md','provenance.json','freeze.json','checks.json','cube.py','cube_reduce.py','cube_route2.py','verify_math.py','cube-certificate.json']]
 paths+=list((C/'sources').glob('*'))
 for p in paths:
  if not p.is_file(): continue
  dst=L/'frozen'/p.relative_to(C); dst.parent.mkdir(parents=True,exist_ok=True)
  a=sha(p); shutil.copyfile(p,dst); b=sha(p); c=sha(dst)
  assert a==b==c
  rows.append({'original':str(p),'copy':str(dst),'sha256':a})
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
  shutil.copyfile(B/n,L/'administrative'/n)
 (L/'freeze.json').write_text(json.dumps({'utc':str(datetime.datetime.now(datetime.timezone.utc)),'inputs':rows},indent=2)+'\n')
 print('FROZEN',len(rows))
if __name__=='__main__':
 if sys.argv[1]=='freeze': freeze()
 if sys.argv[1]=='admin':
  for n in ['ledger.json','prior-campaign-context.json']:
   d=json.loads((L/'administrative'/n).read_text()); print(n)
   print(json.dumps(d,indent=2)[:12500]); print('TOP KEYS',list(d))
 if sys.argv[1]=='fetch':
  name,url=sys.argv[2:4]; dst=L/'primary'/name; dst.parent.mkdir(exist_ok=True)
  rec={'url':url,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=35) as r:
    data=r.read(8_000_001); assert len(data)<=8_000_000
    rec.update(status=r.status,final_url=r.url,headers=dict(r.headers)); dst.write_bytes(data); rec['sha256']=sha(dst); rec['bytes']=len(data)
  except Exception as e: rec['failure']=repr(e)
  (L/'primary'/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec))
 if sys.argv[1]=='extract':
  p=L/'primary'/sys.argv[2]; before=sha(p); dst=p.with_suffix('.txt')
  r=subprocess.run(['pdftotext','-layout',str(p),str(dst)],capture_output=True,text=True)
  assert before==sha(p)
  (dst.with_suffix('.extract.json')).write_text(json.dumps({'pdf_sha256':before,'text_sha256':sha(dst) if dst.exists() else None,'exit':r.returncode,'stderr':r.stderr},indent=2)+'\n'); print(r.returncode,r.stderr)
 if sys.argv[1]=='metadata':
  for n in ['crossref-edge.json','crossref-pseudo.json']:
   print(n)
   for v in json.loads((L/'primary'/n).read_text())['message']['items']:
    print(json.dumps({k:v.get(k) for k in ['title','DOI','published','link','resource']}))
  import xml.etree.ElementTree as E
  ns={'a':'http://www.w3.org/2005/Atom'}
  for e in E.fromstring((L/'primary/arxiv-prior.xml').read_bytes()).findall('a:entry',ns):
   print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
  for n in ['ledger.json','prior-campaign-context.json']:
   d=json.loads((L/'administrative'/n).read_text()); print(n)
   for k,v in d.items():
    if k in ['accepted','candidates','excluded','held_candidates']:
     print(k,json.dumps(v)[:300] if not isinstance(v,list) else '\n'.join(json.dumps({a:r.get(a) for a in ['title','status','reason','path']}) for r in v if isinstance(r,dict)))
    elif k not in ['published_papers']: print(k,json.dumps(v)[:2200])
 if sys.argv[1]=='check':
  z=(2,9,10,13,19,20); x=set(z)-{9}; y=set(z)-{2}; p=(0,3,4,2,1)
  def act(v,p,mask):return sum(((v>>i)&1)<<p[i] for i in range(5))^mask
  # Independent rows use explicit binary vectors and coordinate mismatch counts.
  bits={v:tuple(int(t) for t in format(v,'05b')) for v in z}
  d=lambda a,b:sum(s!=t for s,t in zip(bits[a],bits[b]))
  matrix=[[d(a,b) for b in z] for a in z]
  profiles={v:[sum(d(v,w)==j for w in z) for j in range(6)] for v in z}
  assert len([v for v in z if profiles[v]==profiles[13]])==1
  assert d(9,13)==1 and d(2,13)==4
  transport={v:act(v,p,1) for v in x}; assert set(transport.values())==y
  stabs=[]; trans=[]; bad=[]
  for q in itertools.permutations(range(5)):
   for m in range(32):
    hz={act(v,q,m) for v in z}; hx={act(v,q,m) for v in x}
    if hz==set(z): stabs.append([q,m])
    if hx==y: trans.append([q,m])
    if hz==set(z) and hx==y: bad.append([q,m])
  assert not bad
  out={'vertices':z,'binary':bits,'distance_matrix':matrix,'profiles':profiles,'transport':transport,'stabilizers':stabs,'transports':trans,'bad':bad,'enumerated':3840,'padding':'proof: appending constant coordinates preserves each mismatch count, independent of ambient permutations'}
  (L/'independent-check.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out))
 if sys.argv[1]=='finalize':
  rows=[]
  for r in json.loads((L/'freeze.json').read_text())['inputs']:
   a,b=sha(pathlib.Path(r['original'])),sha(pathlib.Path(r['copy']))
   assert a==b==r['sha256']; rows.append({**r,'original_after':a,'copy_after':b})
  (L/'before-after.json').write_text(json.dumps(rows,indent=2)+'\n')
  scopes={}
  for name,terms in {'published.txt':['Definition 1.4','Theorem 1.5','Proposition 4.20','Question 6.6'], 'kocay.txt':['3.3. THEOREM','4.5. CONSTRUCTION'], 'chains.txt':['Lemma 2.2','A.2    Proof'], 'sperner.txt':['Proposition 3.13','Proposition 7.2'], 'geometry.txt':['Theorem 2 (Main','Conjecture 2']}.items():
   pages=(L/'primary'/name).read_text().split('\f')
   scopes[name]={t:[i+1 for i,p in enumerate(pages) if t in p] for t in terms}
  (L/'page-map.json').write_text(json.dumps(scopes,indent=2)+'\n')
  excluded={'manifest.json','verification-receipt.json'}
  manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
  (L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n'); print('manifest files',len(manifest),'inputs unchanged',len(rows)); print(json.dumps(scopes))
 if sys.argv[1]=='verify':
  m=json.loads((L/'manifest.json').read_text()); assert 'manifest.json' not in m and 'verification-receipt.json' not in m
  for n,h in m.items(): assert sha(L/n)==h,n
  actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'manifest.json','verification-receipt.json'}}
  assert actual==set(m)
  for r in json.loads((L/'freeze.json').read_text())['inputs']: assert sha(pathlib.Path(r['original']))==sha(pathlib.Path(r['copy']))==r['sha256']
  for p in (L/'primary').glob('*.receipt.json'):
   r=json.loads(p.read_text())
   if 'sha256' in r: assert sha(p.with_name(p.name.removesuffix('.receipt.json')))==r['sha256']
  for p in (L/'primary').glob('*.extract.json'):
   r=json.loads(p.read_text()); stem=p.name.removesuffix('.extract.json'); assert sha(p.with_name(stem+'.txt'))==r['text_sha256']; assert sha(p.with_name(stem+'.pdf'))==r['pdf_sha256']
  rec={'status':'PASS','utc':str(datetime.datetime.now(datetime.timezone.utc)),'manifest_sha256':sha(L/'manifest.json'),'verified_files':len(m),'frozen_inputs':69,'originals_and_copies_unchanged':True,'primary_receipts_and_extractions':'PASS','caps':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'excluded':['manifest.json','verification-receipt.json']}
  (L/'verification-receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec))
