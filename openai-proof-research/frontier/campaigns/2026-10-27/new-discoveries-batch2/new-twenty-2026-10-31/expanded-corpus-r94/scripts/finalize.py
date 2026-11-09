from pathlib import Path
import json,hashlib,datetime,os
D=Path(__file__).resolve().parents[1];x=json.load(open(D/'results.json'));assert len(x)==20
for key,v in x.items():
 p=Path(v['provenance']['chunk']);line=p.read_bytes().splitlines(keepends=True)[v['provenance']['line_1based']-1]
 assert line==(D/'raw'/f'{key}.jsonl').read_bytes()
 assert hashlib.sha256(line).hexdigest()==v['provenance']['raw_sha256']
 assert hashlib.sha256(v['statement'].encode()).hexdigest()==v['provenance']['statement_utf8_sha256']
 assert v['credit']==0 and v['lean_endpoint']is None
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if 'sha256'in r:assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256']
receipts=[json.load(open(p))for p in(D/'logs').glob('*.receipt.json')]
coverage={}
for stem in ['chomp','chomp-three','graphs-terminal','graphs-antimagic','graphs-product','uber','coloring','domino-deep','matroid']:
 p=D/'outputs'/f'{stem}.json'
 if p.exists():
  o=json.load(open(p));coverage[stem]={'records':len(o),'last':o[-1]if stem in ['chomp','chomp-three']else None}
coverage['foata9']=sum(json.load(open(p))['count']for p in(D/'outputs').glob('foata-exhaust-9-*.json'))
coverage['terminal_connected_samples']=sum(o['graphs']for o in json.load(open(D/'outputs/graphs-terminal.json')))
coverage['antimagic_twinfree_samples']=sum(o['eligible']for o in json.load(open(D/'outputs/graphs-antimagic.json')))
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  cwd=(p/'cwd').resolve()
  if cwd==D and ('scripts/'in cmd) and ('exec_command'not in cmd)and('finalize.py'not in cmd):active.append({'pid':p.name,'command':cmd})
 except (OSError,PermissionError):pass
(D/'outputs/final-validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'raw_records_validated':20,'source_receipts_validated':True,'result_keys_validated':20,'coverage':coverage,'peak_search_process_RSS':max(r.get('sampled_process_rss_peak_bytes',0)for r in receipts),'search_receipts':len(receipts),'nonzero_receipts':[r for r in receipts if r.get('returncode')],'active_lane_script_processes':active},indent=2)+'\n')
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest()for p in D.rglob('*')if p.is_file()and p.name!='SHA256SUMS.json'}
(D/'SHA256SUMS.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'files_hashed':len(manifest),'coverage':coverage,'active':active},indent=2))
