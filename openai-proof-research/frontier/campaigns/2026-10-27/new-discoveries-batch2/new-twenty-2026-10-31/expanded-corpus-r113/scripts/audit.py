import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();results=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text());assert len(results)==20 and set(map(int,results))==set(res['ids']);checked={}
for i,o in results.items():
 p=D/f'raw/{i}.jsonl';raw=p.read_bytes();pr=o['provenance'];assert raw.endswith(b'\n');assert sha(raw)==pr['raw_sha256'];assert sha(o['statement'].encode())==pr['statement_utf8_sha256'];c=pathlib.Path(pr['chunk'])
 if str(c) not in checked:
  b=c.read_bytes();assert sha(b)==pr['chunk_sha256'];checked[str(c)]=b.splitlines(keepends=True)
 assert checked[str(c)][pr['line_1based']-1]==raw
 sr=o['source_receipt'];assert sha(pathlib.Path(sr['path']).read_bytes())==sr['sha256'];assert o['accepted_credit']==0 and o['lean_packet'] is None
# Inspect /proc using each process's cwd, not command substring matches from other lanes.
active=[]
for p in pathlib.Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name) in [os.getpid(),os.getppid()]:continue
 try:
  if p.joinpath('cwd').resolve()==D:
   cmd=p.joinpath('cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
   if p.joinpath('comm').read_text().strip() in ['python','python3','node','MainThread'] and any(s in cmd for s in ['scripts/digits','scripts/stamps','scripts/pinwheel','scripts/finite','scripts/designs','scripts/equalpart']):active.append({'pid':int(p.name),'cmd':cmd})
 except (OSError,PermissionError):pass
assert not active,active
inventory={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['artifact-hashes.json'] and not str(p).endswith('logs/audit.log') and not str(p).endswith('logs/audit.receipt.json')}
(D/'outputs/artifact-hashes.json').write_text(json.dumps(inventory,indent=2)+'\n');print(json.dumps({'result_count':len(results),'verified_chunks':len(checked),'verified_raw_lines':20,'verified_source_bodies':20,'active_numerical_jobs':active,'files_hashed':len(inventory)},indent=2))
