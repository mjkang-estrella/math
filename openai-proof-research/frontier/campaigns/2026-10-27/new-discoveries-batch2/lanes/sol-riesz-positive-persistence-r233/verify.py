import pathlib,json,hashlib,datetime,resource,os
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());errors=[];counts={'manifest':0,'scientific_original_and_copy':0,'administrative_snapshot':0,'pdf_text_bindings':0}
for name,h in m['files'].items():
 p=L/name
 if not p.is_file() or sha(p)!=h:errors.append({'manifest_mismatch':name})
 counts['manifest']+=1
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
if actual!=set(m['files']):errors.append({'file_set_mismatch':sorted(actual.symmetric_difference(m['files']))})
for row in map(json.loads,(L/'provenance.jsonl').read_text().splitlines()):
 if sha(row['copy'])!=row['sha256']:errors.append({'copy_mismatch':row})
 if row['administrative']:counts['administrative_snapshot']+=1
 else:
  if sha(row['original'])!=row['sha256']:errors.append({'original_changed':row})
  counts['scientific_original_and_copy']+=1
for row in json.loads((L/'text-bindings.json').read_text()):
 if sha(row['pdf'])!=row['pdf_sha256'] or sha(row['text'])!=row['text_sha256']:errors.append({'binding_mismatch':row})
 counts['pdf_text_bindings']+=1
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':not errors,'errors':errors,'counts':counts,'manifest_sha256':sha(L/'final-manifest.json'),'limits':{'AS':resource.getrlimit(resource.RLIMIT_AS)[0],'CPU':resource.getrlimit(resource.RLIMIT_CPU)[0],'group_RSS_bytes':512*1024*1024,'wall_seconds':230},'environment':{k:os.environ.get(k) for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE']},'result':'Integrity verification only; no scientific solution or novelty clearance implied.'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(bool(errors))
