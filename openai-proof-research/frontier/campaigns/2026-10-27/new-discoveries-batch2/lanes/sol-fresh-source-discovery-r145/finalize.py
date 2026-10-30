import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if len(sys.argv)>1 and sys.argv[1]=='verify':
 m=json.loads((L/'finalmanifest.json').read_text());bad=[]
 for x in m['files']:
  p=L/x['path'];b=p.read_bytes()
  if len(b)!=x['bytes'] or sha(b)!=x['sha256']:bad.append(x['path'])
 r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),entries=len(m['files']),failures=bad,verified=not bad,manifest_self_reference=False)
 write('manifest-verification.json',r);print(r);sys.exit(bool(bad))
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
inherited=[]
for rel in ['sol-fresh-source-discovery-r133/history-receipt.json','sol-fresh-source-discovery-r133/history-aliases.jsonl.gz','sol-fresh-source-discovery-r137/history-receipt.json','sol-fresh-source-discovery-r141/provenance.json','sol-fresh-source-discovery-r142/provenance.json','sol-fresh-source-discovery-r144/registry-limits.json']:
 p=B/'lanes'/rel;b=p.read_bytes();inherited.append(dict(path=str(p),sha256=sha(b),bytes=len(b)))
hist=[]
for p in sorted(L.glob('history-*.json')):
 j=json.loads(p.read_bytes())
 if isinstance(j,dict) and 'pattern' in j:
  hist.append({k:j[k] for k in ['utc','pattern','paths','unique_bodies','unchanged','changed','missing','oversize','global_cutoff','retained_r111_r113'] if k in j})
write('provenance.json',dict(finalized_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),outcome='ZERO: full Conjecture5.4 unresolved',source=dict(doi='10.5281/zenodo.21706797',label='Conjecture5.4',version='1.3',scope='Every finite connected simple graph; 2s(L(G))<=c(G)+1',primary_pdf='sources/paone.pdf'),counts_observed=dict(additional=9,total=39,next=40),count_mutations=False,write_scope=str(L),http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()],history=hist,inherited=inherited,registry=json.loads((L/'registry-screen.json').read_text()),checks=json.loads((L/'check-results.json').read_text()),structure=json.loads((L/'structure-results.json').read_text()),guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),unchanged=True,AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,env={'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},limit='sampled process-group peaks do not bound unsampled transients'),access_limits=['Zagreb403: stopped, no bypass','Author metric PDF404; actual arxiv HTML available','Both Omega intervals capped300; no current proof-body novelty clearance','No exhaustive literature/priority claim','Search tool timestamps not individually archived; bounded turn-time search only'],failed_runs=['checks-run.log: missing networkx','structure-run.log: missing __file__','structure-run-2.log: singular matrix invalidated inverse-only solve'],successful_runs=['checks-run-2.log','structure-run-3.log','registry-run.log'],searches=['Zagreb exact title authors source ID','Annor 2506.03646 title conjecture counterexample','metric dimension cyclomatic conjecture 2026','Chen Ma mixed metric dimension 2607.27573 2608.17944','Line-Graph Signature Beyond title Paone bound conjecture','2s(L(G)) c(G)','Sharp bound at fixed cyclomatic number','site:github.com/the-omega-institute/trureturing line signature'],actions=dict(children=False,git=False,shared_edits=False,public_mutations=False,browser_tabs=False,Lean=False,manuscript=False),remaining=['full ordinary proof or exact source counterexample','current target-specific registry-body and classical eligibility clearance','independent review before Lean/manuscript']))
excluded={'finalmanifest.json','manifest-verification.json','finalize-run.log','verify-run.log'}
files=[]
for p in sorted(L.rglob('*')):
 if not p.is_file() or p.name in excluded:continue
 b=p.read_bytes();files.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
science=[x for x in files if x['path'].startswith('sources/') or x['path'] in ['checks.py','tinygraph.py','structure.py','check-results.json','structure-results.json','discovery.md','SUMMARY.md','run-checks.sh']]
write('scientific-freeze.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=science,NEXT_excluded=True,scope='primary bytes, mathematical record and checks; mutable context separate'))
p=L/'scientific-freeze.json';b=p.read_bytes();files=[x for x in files if x['path']!='scientific-freeze.json'];files.append(dict(path=p.name,bytes=len(b),sha256=sha(b)))
write('finalmanifest.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=files,excluded=sorted(excluded),exclusion_reason='manifest self-reference, verification receipt and post-finalization stdout logs'))
print(dict(files=len(files),scientific_files=len(science),guard_sha256=sha(guard.read_bytes())))
