from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
retr=[json.loads(s) for s in (L/'retrieval.jsonl').read_text().splitlines()]
for r in retr:assert h(Path(r['path']))==r['sha256'],r['path']
old=json.loads((L/'source-bindings.json').read_text())
for r in old:assert h(Path(r['original']))==r['sha256'],r['original']
bindings=[]
for p in sorted((L/'primary').glob('*.pdf')):
 if not p.read_bytes().startswith(b'%PDF'):continue
 t=p.with_suffix('.txt')
 bindings.append({'pdf':str(p.resolve()),'pdf_sha256':h(p),'text':str(t.resolve()),'text_sha256':h(t),'extraction':'pdftotext -layout; original response bound in retrieval.jsonl before extraction'})
(L/'primary-text-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'HOLD; no source-question resolution','counts':{'additional':9,'total':39,'next':40},'credit':0,'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','limits':{'AS_MiB':512,'sampled_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'OPENBLAS_NUM_THREADS':1,'OMP_NUM_THREADS':1,'PYTHONDONTWRITEBYTECODE':1},'original_attribution':'Głąb–Marchwicki, arXiv1911.01206v1 Problem2.12,4Nov2019; ResultsMath75:141(2020)','restatement':'Głąb–Prus-Wiśniowski2512.17285v1 Problem30','finite_prefix':'Marchwicki–Żmija2508.13016v1 Lemma2.1','registry_status':'PARKED denied historical intervals; no current head checked','history_scope':'direct bounded SUMMARY/SCOUTING/discovery current-batch files only','source_freeze':'r236 immutable references hashed before reading; newly retrieved bytes saved+hashed before extraction; verified again at finalization and in separate verifier','administrative':'snapshot only','scientific_mutations':'none to original referenced files','external_mutations':False,'failures':['bs4 unavailable; preserved responses parsed locally','inspect.py shadowed stdlib; renamed inspect_sources.py','wrong-object1208.0159','wrong-object2601.04941','generic Bing results not evidence'],'limitations':['full additive question unresolved','no exhaustive current citation or registry clearance','eight source families are not eight fresh nominations','some original posing documents unlocated']}
(L/'provenance.json').write_text(json.dumps(prov,indent=2,ensure_ascii=False)+'\n')
exclude={'manifest.json','verification-receipt.json'}
files={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclude}
(L/'manifest.json').write_text(json.dumps({'algorithm':'sha256','excludes':sorted(exclude),'files':files},indent=2)+'\n')
print('manifest files',len(files),'primary bindings',len(bindings),'immutable originals verified',len(old))
