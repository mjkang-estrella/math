from pathlib import Path
import hashlib,json,datetime,subprocess,sys,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
for r in rows:
 if 'path' in r:assert sha(Path(r['path']))==r['sha256']
versions=[]
for p in (L/'sources').glob('*.xml'):
 ns={'a':'http://www.w3.org/2005/Atom'}
 for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):
  versions.append({k:e.find('a:'+k,ns).text for k in ['id','title','published','updated']})
(L/'versions.json').write_text(json.dumps(versions,indent=2))
r=subprocess.run([sys.executable,str(L/'checks.py')],text=True,capture_output=True)
(L/'checks.json').write_text(json.dumps({'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr},indent=2));assert r.returncode==0
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'guard':{'path':str(guard),'sha256':sha(guard),'AS_bytes':512*1024**2,'sampled_process_group_RSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'sampling_limit':'40ms process group RSS; unsampled transients not ruled out'},'http_records':len(rows),'pdfs':[{'path':str(p.relative_to(L)),'sha256':sha(p),'text_sha256':sha(p.with_suffix('.txt'))} for p in sorted((L/'sources').glob('*.pdf'))],'history_index':{'path':'frozen/history-index.json','sha256':sha(L/'frozen/history-index.json'),'records':len(json.loads((L/'frozen/history-index.json').read_text())['records'])},'scientific_binding':'HTTP body is frozen in sources before extraction. http.jsonl hashes checked before/after; no mutable scientific original overwritten. Coordination copies bound in freeze.json. Administrative originals are snapshots only.','limits':['No current complete registry head','No original Vietoris1958 proof body','No exhaustive citing-body or publisher-version clearance'],'count_credit_requested':0}
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
base='OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python '+str(guard)+' python '
(L/'RUN.md').write_text('# Exact replay\n\nRun from any working directory; paths are absolute. All helpers remain under the fixed guard.\n\n```bash\n'+base+str(L/'checks.py')+'\n'+base+str(L/'verify.py')+'\n```\n\nSources and failed-search metadata are retained; work.py supports bounded arXiv retrieval, but replay does not require network retrieval. No historical inaccessible interval needs reopening. finalize.py regenerates provenance, checks output and manifest; after any regeneration, run verify.py in a separate guarded process. Manifest excludes itself and verification-receipt.json.\n')
excluded={'finalmanifest.json','verification-receipt.json'}
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
(L/'finalmanifest.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps({'files':len(manifest),'manifest_sha256':sha(L/'finalmanifest.json'),'checks':'PASS'}))
