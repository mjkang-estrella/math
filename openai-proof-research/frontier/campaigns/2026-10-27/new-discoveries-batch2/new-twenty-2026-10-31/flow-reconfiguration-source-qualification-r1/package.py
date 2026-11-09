import pathlib,json,hashlib,datetime,resource,os,re
P=pathlib.Path(__file__).resolve().parent; C=P.parent; R=C/'expanded-corpus-r261'; ROOT=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def sha(b):return hashlib.sha256(b).hexdigest()
reads=[]
def read(p):
 b=p.read_bytes();reads.append({'path':str(p),'bytes':len(b),'sha256':sha(b),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()});return b
for p in [ROOT/'sources/upstream.json',ROOT/'sources/CONTENTS.md',ROOT/'sources/preprints-tree.json',C.parent/'ledger.json',C.parent/'prior-campaign-context.json',C/'ledger.json',C/'STATUS.md',R/'SUMMARY.md',R/'MECHANISMS.md',R/'source-read-inventory.json',R/'history-375537.txt',R/'historical-context-375537.txt',R/'verification.json',R/'fetch-receipts.jsonl',R/'text-job-log.json']:
 read(p)
d=json.loads(read(R/'results.json')); bindings=[]
for key,v in d.items():
 p=v['raw_provenance'];raw=read(pathlib.Path(p['literal_raw_file']));actual=sha(raw);bindings.append({'id':key,'raw_match':actual==p['raw_sha256'],'statement_match':sha(v['record']['statement'].encode())==p['statement_sha256']})
v=d['375537'];p=v['raw_provenance'];chunk=read(pathlib.Path(p['chunk']));line=chunk.splitlines(keepends=True)[p['one_based_line']-1]
reg=[]
for name in ['openai-OAI-Combinatorics.json','openai-OAI-Algorithms.json','openai-OAI-Optimization.json','pool-tree.json','omega-tree.json']:
 f=C/'common-basis-source-review-r1/receipts'/name
 if not f.exists():continue
 j=json.loads(read(f)); matches=[x['path'] for x in j.get('tree',[]) if re.search(r'nowhere.?zero|flow.?reconfig|375537|2610.40863|2512.17342|2606.24685',x.get('path',''),re.I)]
 reg.append({'path':str(f),'truncated':j.get('truncated'),'sha':j.get('sha'),'matching_paths':matches,'scope':'dated cached tree path screen only; no full current tree/code clearance'})
for p in [R/'sources/pool-current.lean',R/'sources/pool-current-projects.yml',R/'sources/pool-maxflow.lean',C/'common-basis-root-final-r1/openai.receipt.json',C/'common-basis-root-final-r1/pool.receipt.json',C/'common-basis-root-final-r1/omega.receipt.json']:
 read(p)
e={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'raw_bindings_20':bindings,'target_chunk_hash_match':sha(chunk)==p.get('chunk_sha256') if isinstance(p,dict) else sha(chunk)==v['raw_provenance']['chunk_sha256'],'target_line_match':line==pathlib.Path(v['raw_provenance']['literal_raw_file']).read_bytes(),'target_provenance':v['raw_provenance'],'registry_screen':reg,'reads':reads,'expanded_pdf_extraction':{'first_download':'HTTP 200 but pdftotext xref/trailer failure','standard_advertised_download':'HTTP 200; pdftotext exit 0; full body available','first_download_bytes':(P/'goel-expanded.pdf').stat().st_size,'standard_download_bytes':(P/'goel-expanded-download.pdf').stat().st_size},'companion_extraction':json.loads((P/'companion-text-status.json').read_text()),'read_depth':{'cranston':'Introduction, Section 2, Sections 3–4 proof passages; Section 5 FRC/cycle degeneracy and Figure captions; selected Section 6 bridge','esperet_v1':'Sections 2.1–2.4, Lemma 5.5, D_m/duality passages','esperet_v2_v3':'Sections 2.1–2.2 and Lemma 5.5; not full papers','esperet_v4':'Sections 2–3 proofs, selected Section 4–5 examples, Lemma 5.5 and Theorem 5.6','goel_arxiv':'Introduction and all Section 7 lifting proof bodies; not whole Eulerian proof','goel_expanded':'Introduction and provenance dependency paragraphs; not 159-page proof audit','goel_companion':'Introduction, all Sections 2–6 statements and proofs; no complete audit of later parts','figures':'captions/proof mechanisms only; no full visual edge transcription','supporting_code':'not fetched or replayed'},'resource_policy':{'fetch_text_jobs':'finite, sequential, timeout 140s; scripts CPU120, AS6GiB, affinity<=2','initial_short_read_commands':'not explicitly affinity-pinned; no heavy calculation','graph_search':False,'solver':False,'Lean':False,'child_agents':False,'all_launched_jobs_finished':True},'accepted_credit':0}
# Public response cookies are irrelevant to provenance and are removed from the local receipt.
f=P/'fetch-receipts.jsonl'
if f.exists():
 rows=[json.loads(x) for x in f.read_text().splitlines()]
 for r in rows:
  if 'headers' in r:r['headers']={k:v for k,v in r['headers'].items() if k.lower() not in ('set-cookie','cookie')}
 f.write_text(''.join(json.dumps(r)+'\n' for r in rows))
(P/'evidence.json').write_text(json.dumps(e,indent=2))
e['workspace_incident']={'description':'One accidental new four-byte placeholder was transiently created at campaign/review-placeholder-do-not-create by a patch; immediately deleted in the next patch. No pre-existing author or shared file was changed; no residual file remains.','residual_exists':(C/'review-placeholder-do-not-create').exists()}
(P/'evidence.json').write_text(json.dumps(e,indent=2))
frozen=json.loads((P/'frozen-inputs.json').read_text());checks=[{'path':s,'expected':h,'actual':sha(pathlib.Path(s).read_bytes())} for s,h in frozen.items()]
(P/'frozen-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'count':len(checks),'all_match':all(x['expected']==x['actual'] for x in checks),'files':checks},indent=2))
manifest={str(p.relative_to(P)):sha(p.read_bytes()) for p in sorted(P.rglob('*')) if p.is_file() and p.name!='hashmanifest.json'}
(P/'hashmanifest.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps({'frozen_count':len(checks),'frozen_all_match':all(x['expected']==x['actual'] for x in checks),'raw_bindings_all_match':all(x['raw_match'] and x['statement_match'] for x in bindings),'target_line_match':e['target_line_match'],'registry':reg,'manifest_files':len(manifest)},indent=2))
