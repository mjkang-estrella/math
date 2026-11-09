import os,pathlib,json,hashlib,datetime,sys
L=pathlib.Path.cwd();R=json.load(open('results.json'));reservation=json.load(open('reservation.json'));H=lambda b:hashlib.sha256(b).hexdigest();errors=[]
assert len(R)==20 and set(map(int,R))==set(reservation['ids'])
for i,r in R.items():
 b=(L/r['raw_file']).read_bytes()
 if not b.endswith(b'\n') or H(b)!=r['raw_provenance']['raw_sha256']:errors.append('raw '+i)
 if H(json.loads(b)['statement'].encode())!=r['statement_sha256']:errors.append('statement '+i)
 for f in r['sources']:
  if H((L/f['path']).read_bytes())!=f['sha256']:errors.append('source '+f['path'])
 for p in r['search_outputs']:
  if not(L/p).exists():errors.append('missing output '+p)
j=json.load(open('outputs/wachs8.json'));assert len(j['bottoms'])==j['elements']==6144 and not j['counterexamples'];assert len({x['index']for x in j['bottoms']})==6144
jobs=[]
for p in pathlib.Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();comm=(p/'comm').read_text().strip();cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if cwd==L and comm in ['python','python3','lean','leanchecker','pdftotext','timeout']:jobs.append({'pid':int(p.name),'comm':comm,'cmd':cmd})
 except (OSError,PermissionError):pass
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':len(R),'reserved_ids_match':True,'credit':sum(r['accepted_credit']for r in R.values()),'validation_errors':errors,'remaining_lane_compute_jobs':jobs,'n8_complete':True,'python':sys.version,'limitations':['bounded pass, not the requested multi-hour depth','snake triangulation search unimplemented','pip temporary/cache confinement not attested','early failed Lean logs overwritten','no new endpoint or acceptance-grade Lean packet']}
json.dump(report,open('outputs/handback-check.json','w'),indent=2)
files=[]
for folder in ['raw','sources','receipts','scripts','outputs','lean']:
 for p in (L/folder).rglob('*'):
  if p.is_file() and '__pycache__'not in p.parts:files.append(p)
files +=[L/'SUMMARY.md',L/'SOURCE-AND-ATTEMPTS.md',L/'results.json',L/'reservation.json',L/'TASK.txt']
(L/'manifest.sha256').write_text(''.join(H(p.read_bytes())+'  '+str(p.relative_to(L))+'\n'for p in sorted(set(files))))
print(json.dumps(report,indent=2))
assert not errors and not jobs
