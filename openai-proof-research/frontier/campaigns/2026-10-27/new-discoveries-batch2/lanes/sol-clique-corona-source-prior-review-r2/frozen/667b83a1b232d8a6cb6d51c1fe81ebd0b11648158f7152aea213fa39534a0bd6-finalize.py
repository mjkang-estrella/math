from pathlib import Path
import hashlib,json,datetime,os
L=Path(__file__).resolve().parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
hist=json.loads((L/'history-receipt.json').read_text())
# Record explicit generated-copy/counterpart pairs already present in inherited index.
byhash={};pairs=[]
for p,h,z in hist['records']:
 byhash.setdefault(h,[]).append(p)
for h,ps in byhash.items():
 if len(ps)>1:
  candidates=[p for p in ps if not any('/'+x+'/' in p for x in ['private','author','frozen','replay','extracted','copy','payload'])]
  primary=min(candidates or ps,key=lambda p:(len(p),p))
  for p in ps:
   if p!=primary:pairs.append(dict(path=p,counterpart=primary,sha256=h,role='identical retained counterpart; no independent novelty evidence'))
save('history-qualification.json',dict(inherited_index_records=len(hist['records']),changed_new=len(hist['changed_or_new']),bases=hist['bases'],identical_counterparts=pairs,original_r111_r113=hist['original_r111_r113'],policy='Reuse qualified originals across all campaign history. Known generated source/build/extraction/context directories were not searched for new originals. Existing indexed records retained, including private scientific originals; no entire lane or date cutoff. A byte-identical secondary counterpart is not independent science.',limits='Qualification inherited from r157/r159/r162/r164/r167; no claim every differently named historical note has been read.'))
save('failures.json',dict(command_failures=[],retrieval_limits=[dict(action='Google search',result='HTML redirect/challenge; no follow-up challenge or bypass',evidence='search1.html'),dict(action='Bing search',result='unhelpful dictionary results, no scientific inference',evidence='bing.html'),dict(action='2017 survey guessed PDF URL',result='HTTP404; URL retained in http.jsonl'),dict(action='2016 Elsevier fulltext API',result='HTTP200 metadata-only XML; not a theorem body',evidence='sources/corona2016.xml'),dict(action='2016 ScienceDirect',result='HTTP403 once, no retry',evidence='http.jsonl')],warnings=['Poppler forest PDF font-type mismatch warning; text extracted, no visual verification claimed','Initial large context output truncated; bounded reads and preserved full context copies used','Initial native shell read used semicolon separators; presentation-rule deviation'],resource_deviations=[],scientific_failed_routes=['Zhan Theorem5 global-endpoint rotation does not preserve fixed endpoints','Simple old nonunimodal degree-four bases need not remain nonunimodal under a leaf corona (actual old source example)']))
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
source_records=[]
for rec in http:
 if 'sha256' in rec:
  p=L/'sources'/rec['name'];assert p.is_file() and sha(p)==rec['sha256'];source_records.append(rec)
base=[]
for rel in ['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/sources/omega-fixed-delta.json','sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','sol-fresh-source-discovery-r157/sources/omega-delta.json','sol-fresh-source-discovery-r157/sources/openai-delta.json','sol-fresh-source-discovery-r167/sources/omega-delta.json','sol-fresh-source-discovery-r167/sources/openai-contents.md']:
 p=L.parent/rel;base.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
save('provenance.json',dict(utc=now,local_date='2026-10-29',timezone='America/Los_Angeles',lane=str(L),scope='solo research, no children/git/shared writes/public mutations/browser/Lean/manuscript',result='ordinary full refutation candidate',eligibility='HOLD: independent root mathematics/substantive/novelty review; unread closest2016 and survey bodies',source_target=dict(doi='10.26493/1855-3974.3383.3c7',number='Conjecture6.1',printed_page=20,global_hypotheses='finite simple graph without isolated vertices; integer p>=1',quantifiers='every G, every p>=1',version='journal-hosted accepted manuscript; published2026-08-05',sha256=sha(L/'sources/corona.pdf')),witness=dict(r=100000,s=225985,base='join(rK3,sK1)',attachment='K1',base_vertices=525985,corona_vertices=1051970),proof='PROOF.md',checks='checks.py',full_proof_vs_checks='ordinary concentration proof refutes source; exact rational diagnostics and tiny graph controls are separate; no large coefficient enumeration',retrievals=source_records,guard=dict(path=str(guard),sha256=sha(guard),as_bytes=512*1024*1024,group_rss_bytes=512*1024*1024,cpu_seconds=210,wall_seconds=230,sample_ms=40,required_env={'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},cap_increases=False,unsampled_transients='not ruled out'),inherited_registry_inputs=base,registry_heads=dict(omega='d36a58e865e46580f127ef7a09d64ccbc2370296',openai='4eaee87548250b2682affda7d05d947c05554bae'),registry_limits=['aa026->a19a->490f300-path caps retained','first1000Problems incomplete','no all-body registry clearance','no latest HEAD chase'],not_performed=['Lean','manuscript','independent review','acceptance','count edit','external posting']))
# Freeze mathematical/source payload separately from operational manifests.
scientific=[p for p in L.rglob('*') if p.is_file() and (p.parent.name=='sources' or p.name in ['PROOF.md','SUMMARY.md','discovery.md','progress.md','checks.py','checks.json','provenance.json','history-receipt.json','history-qualification.json','statement-alias-screen.json','pre-download-screen.json','chord-alias-screen.json','antecedent-alias-screen.json','registry-screen.json'])]
save('scientific-freeze.json',dict(utc=now,status='ordinary full candidate only; eligibility HOLD',files={str(p.relative_to(L)):sha(p) for p in sorted(scientific)},excludes='operational manifests/verification receipts/context/search logs; no formal certificate'))
excluded={'finalmanifest.json','manifest-verification.json','verification.log'}
save('finalmanifest.json',dict(utc=now,exclusions=sorted(excluded),files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}))
print('freeze and final manifest written')
