import pathlib,json,hashlib,os,datetime,zipfile,re
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(x)==20 and set(map(int,x))==set(ids)
for i,o in x.items():
 p=D/'raw'/f'{i}.jsonl';b=p.read_bytes();pr=o['provenance'];assert b.endswith(b'\n') and hashlib.sha256(b).hexdigest()==pr['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==pr['statement_utf8_sha256']
# Recheck actual chunk binding once per chunk and exact one-based source line.
chunks={}
for i,o in x.items():
 pr=o['provenance'];p=pathlib.Path(pr['chunk'])
 if str(p) not in chunks:
  b=p.read_bytes();chunks[str(p)]=(hashlib.sha256(b).hexdigest(),b.splitlines(keepends=True))
 h,ls=chunks[str(p)];assert h==pr['chunk_sha256'] and ls[pr['line_1based']-1]==(D/'raw'/f'{i}.jsonl').read_bytes()
for name in ['packet-strict','packet-audit','packet-checker']:
 r=json.loads((D/f'logs/{name}.receipt.json').read_text());assert r['returncode']==0 and r['cap_reason'] is None
s=(D/'formal/Eventown.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
a=(D/'logs/packet-audit.log').read_text();count=re.search(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',a);assert count
allowed=['propext','Classical.choice','Quot.sound'];lines=[l for l in a.splitlines() if 'INVENTORY|' in l];assert len(lines)==int(count[1]) and all('|false|' in l for l in lines)
# Identify processes by actual cwd in this lane, excluding the validator and its invocation ancestry.
anc=set();p=os.getpid()
while p>0 and p not in anc:
 anc.add(p)
 try:p=int(next(l.split()[1] for l in pathlib.Path(f'/proc/{p}/status').read_text().splitlines() if l.startswith('PPid:')))
 except (OSError,StopIteration):break
live=[]
for p in pathlib.Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name) in anc:continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if cwd==D or D in cwd.parents:live.append({'pid':int(p.name),'cwd':str(cwd),'command':cmd})
 except (OSError,RuntimeError):pass
(D/'outputs/process-audit.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'own_lane_live_nonancestor_processes':live,'scope':'Processes with resolved cwd in lane, excluding validator/invocation ancestry; no process killing or inspection of unrelated work.'},indent=2)+'\n');assert not live,live
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_id_count':len(x),'literal_provenance_verified':True,'strict_extracted_rebuild':'PASS','leanchecker':'PASS','local_declarations_audited':int(count[1]),'allowed_transitive_axioms':allowed,'no_live_lane_background_processes':True,'accepted_credit':0,'packet_sha256':hashlib.sha256((D/'372630-lean-packet.zip').read_bytes()).hexdigest(),'dependency_trust':'Cached upstream oleans; no full upstream source rebuild or source-to-olean attestation.','resources':'Per-call affinity 2 CPUs, CPU120s, wall140s, sampled main-process RSS6GiB; address space12GiB; full logs retained. One S6 search hit wall cap and has no completed result.'}
(D/'validation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
