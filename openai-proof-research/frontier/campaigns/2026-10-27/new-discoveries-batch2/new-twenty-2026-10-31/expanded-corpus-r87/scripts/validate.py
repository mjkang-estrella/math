from pathlib import Path
import json,hashlib,datetime,os
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
R=json.loads((D/'results.json').read_text());reserve=json.loads((D/'reservation.json').read_text());assert len(R)==20 and set(R)=={str(i) for i in reserve['ids']}
corpus=D.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301';mp=corpus/'manifest.json';M=json.loads(mp.read_text());chunks=[]
for item in M['files']:
 if item['path'].startswith('corpus/mathdb-normalized-chunk-'):
  p=corpus/item['path'];s=sha(p.read_bytes());assert s==item['sha256'];chunks.append({'path':str(p),'sha256':s})
assert len(chunks)==20
for i,o in R.items():
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert json.loads(raw)['statement']==o['statement']
 p=Path(o['provenance']['chunk']);assert sha(p.read_bytes())==o['provenance']['chunk_sha256'];assert p.read_bytes().splitlines(keepends=True)[o['provenance']['line_1based']-1]==raw
 receipt=json.loads((D/o['source_receipts'][0]).read_text());assert receipt['status']==200;assert sha((D/'sources'/receipt['path'].split('/')[-1]).read_bytes())==receipt['sha256']
 assert o['discovery_count_credit']==0 and o['lean']['endpoint'] is None
running=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit() or int(proc.name)==os.getpid():continue
 try:args=proc.joinpath('cmdline').read_bytes().split(b'\0')
 except OSError:continue
 if not args or b'python' not in args[0]:continue
 if any(b'expanded-corpus-r87/scripts/' in a and a.endswith(b'.py') for a in args[1:]):running.append({'pid':int(proc.name),'argv':[a.decode(errors='replace') for a in args if a]})
assert not running,running
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_id_count':len(R),'all_raw_newlines_and_line_bindings_verified':True,'all_20_manifest_chunk_hashes_verified':True,'corpus_manifest':str(mp),'corpus_manifest_sha256':sha(mp.read_bytes()),'chunks':chunks,'primary_pdf_bytes_verified':20,'no_discovery_credit':True,'lean_endpoint':None,'running_lane_python_jobs':running,'limitations':['Not a several-hour run; bounded discovery work only.','No Lean or upstream rebuild performed.','Search scripts are diagnostic and not formal proofs.','Resource RSS receipts are sampled direct-process measurements.','Reservation output_requirement says Exactly40; explicit TASK and actual 20 reserved IDs control this handback.']}
(D/'outputs/final-validation.json').write_text(json.dumps(out,indent=2)+'\n')
files=[]
for p in sorted(D.rglob('*')):
 if not p.is_file() or 'vendor' in p.parts or '__pycache__' in p.parts or p.name=='MANIFEST.json':continue
 files.append({'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())})
(D/'MANIFEST.json').write_text(json.dumps({'utc':out['utc'],'files':files,'excluded':'Lane-local vendor packages and Python bytecode; system dependencies read-only'},indent=2)+'\n')
print(json.dumps({'ids':len(R),'files_hashed':len(files),'chunks_verified':len(chunks),'running_jobs':running,'outcomes':{k:sum(o['outcome']==k for o in R.values()) for k in sorted(set(o['outcome'] for o in R.values()))}},indent=2))
