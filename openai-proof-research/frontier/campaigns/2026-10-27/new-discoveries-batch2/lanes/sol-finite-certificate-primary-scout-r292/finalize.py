import pathlib,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(name,x):(L/name).write_text(json.dumps(x,indent=2)+'\n')
records=json.loads((L/'bindings.json').read_text())
if sys.argv[1]=='repair':
 for r in records:
  if r['kind']=='administrative' and pathlib.Path(r['original']).name=='AGENTS.md':
   p=pathlib.Path(r['original']);assert sha(p)==r['sha256']
   name='AGENTS-batch.md' if 'new-discoveries-batch2' in str(p) else 'AGENTS-ancestor.md'
   q=L/'administrative'/name;q.write_bytes(p.read_bytes());assert sha(q)==r['sha256'];r['copy']=str(q)
 dump('bindings.json',records)
 dump('failures.json',[
  {'kind':'selection failure','issue':'Exact AP campaign duplicate was in early dedup output but missed because display was truncated. r245 has a stronger4n-10 family and another lane formalized n5.','disposition':'Retired AP immediately after untruncated inspection. Zero fresh credit. One pivot to unique sepr; no complete fresh result.'},
  {'kind':'pre-freeze cold reads','issue':'r291 STATUS, upstream.json and first CONTENTS.md lines were initially exposed before freeze.','limit':'No clean pre-read hash custody for these cold-start materials. Actual candidate primary PDF/text bodies and compared historical reports were bound before inspection; final hashes checked.'},
  {'kind':'custody-administrative','issue':'Two administrative AGENTS.md snapshots initially shared a basename; ancestor overwrote batch snapshot. Pre-final audit preserved this mismatch.','repair':'Distinct names restored under guard after checking each original against its original bound hash. Scientific source hashes were unaffected.'},
  {'kind':'semantic retrieval','issue':'au:Dick AND all:Parikh returned an unrelated dark-matter paper 2203.08297v2. Bytes preserved; not used as mathematical evidence.'},
  {'kind':'search preservation','issue':'The first dedup result file was overwritten by the second dedup invocation; first tool transcript still records its result. Second and later dedup files retained.','effect':'No source was changed; bounded dedup limitations remain explicit.'},
  {'kind':'scope limitation','issue':'GitHub landing page establishes current head only, not current recursive catalogue/proof coverage. Forbidden routes not attempted.'},
  {'kind':'unsuccessful check','issue':'Initial n=3 and n=4 minimal-AP trials found no excess over 2n-2; exact maxima among sampled candidates retained in checks-result.json, no exhaustiveness claim.'}
 ])
elif sys.argv[1]=='manifest':
 for r in records:
  for key in (['copy'] if r['kind']=='administrative' else ['original','copy']):assert sha(pathlib.Path(r[key]))==r['sha256'],r
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 dump('provenance.json',dict(date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),guard=str(guard),guard_sha256=sha(guard),environment={'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},caps={'AS_bytes':512*1024*1024,'group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230},source_bindings='bindings.json',access_log='access.json',scientific_before_after='Actual candidate primary PDF/text bodies and historical reports bound before inspection; final hashes checked. Initial r291 STATUS/upstream/catalogue cold-read exceptions are disclosed in failures.json. Final separate verifier repeats hashes.',administrative='Snapshots only; basename collision repaired; no recursive historical copying.',current_registry={'url':'https://github.com/openai/math','head':'4eaee87548250b2682affda7d05d947c05554bae','scope':'Landing-page head, not exhaustive current theorem-body screen.'},counts={'additional':9,'total':39,'next':40},writes_scope=str(L),novelty='No fresh complete result. AP retired duplicate; sepr pivot incomplete.'))
 files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 dump('manifest.json',{'algorithm':'sha256','excludes':['manifest.json','verification-receipt.json'],'files':files})
 print('manifest files',len(files),'bindings',len(records))
