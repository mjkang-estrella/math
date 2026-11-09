import pathlib,json,hashlib,zipfile,re,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((D/'reservation.json').read_text());E=json.loads((D/'extracted.json').read_text());j=json.loads((D/'results.json').read_text())
assert len(j)==20 and set(map(int,j))==set(R['ids'])
M=B/'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json';man=json.loads(M.read_text());lookup={x['path']:x for x in man['files']};chunks=[]
for p in sorted((M.parent/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 b=p.read_bytes();h=sha(b);assert h==lookup['corpus/'+p.name]['sha256'];chunks.append({'name':p.name,'sha256':h})
assert len(chunks)==20
for i,e in E.items():
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==e['provenance']['raw_sha256'];assert sha(e['statement'].encode())==e['provenance']['statement_utf8_sha256'];assert json.loads(raw)['statement']==e['statement']
 p=pathlib.Path(e['provenance']['chunk']);assert p.read_bytes().splitlines(keepends=True)[e['provenance']['line_1based']-1]==raw
for receipt in json.loads((D/'sources/fetch-receipts.json').read_text()):
 if receipt.get('status')!=200:continue
 url=receipt['url'];name=url.rsplit('/',1)[-1] if '/pdf/' in url else ('openai' if '/openai/' in url else 'omega')+'-head.json';assert sha((D/'sources'/name).read_bytes())==receipt['sha256']
rep=json.loads((D/'replay/replay.json').read_text());assert len(rep['steps'])==3 and all(s['returncode']==0 for s in rep['steps']);assert sha((D/'lean/Digits.lean').read_bytes())==rep['source_sha256']
audit=(D/'replay/Audit.log').read_text();assert 'AUDITED_LOCAL_DECLARATIONS|45' in audit and 'sorryAx' not in audit and 'UNSAFE|true' not in audit and 'PARTIAL|true' not in audit
with zipfile.ZipFile(D/'356756-proof-source.zip') as z:
 assert set(z.namelist())=={'Digits.lean','Audit.lean'}
 for name in z.namelist():assert z.read(name)==(D/'lean'/name).read_bytes()
# Only lane-owned jobs, excluding this validator and its parent tool shell.
ps=subprocess.run(['ps','-eo','pid,ppid,comm,args'],capture_output=True,text=True,check=True).stdout
jobs=[l for l in ps.splitlines() if str(D) in l and ('leanchecker' in l or '/scripts/' in l) and 'validate.py' not in l and 'bash -c' not in l]
assert not jobs,jobs
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_ID_count':20,'raw_lines_and_statements_verified':20,'manifest_bound_chunks_verified':chunks,'proof_source_sha256':rep['source_sha256'],'strict_replay_and_leanchecker':'pass','all_local_declarations_audited':45,'self_accepted':0,'lane_background_jobs':jobs,'trust_limits':'external prebuilt dependencies trusted; no full upstream rebuild; bounded prior art and source access'}
(D/'outputs/handback-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='manifest_bound_chunks_verified'},indent=2))
# Manifest excludes itself; mutable logs and all source receipts included at handback.
paths=[p for p in D.rglob('*') if p.is_file() and p.name!='MANIFEST.sha256'];(D/'MANIFEST.sha256').write_text(''.join(f'{sha(p.read_bytes())}  {p.relative_to(D)}\n' for p in sorted(paths)))
