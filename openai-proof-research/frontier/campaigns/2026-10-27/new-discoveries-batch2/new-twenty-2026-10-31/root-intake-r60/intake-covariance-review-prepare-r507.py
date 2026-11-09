"""Root documentary verification and disjoint selection, without mathematical solving."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,importlib.util,collections
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;A=P/'subcritical-covariance-source-review-sol-r1'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'ledger.json')['accepted_new']==57
ready=read(ROOT/'subcritical-covariance-review-r1-ready.json')
assert sha(A/'TASK.txt')==ready['task_sha256'] and read(ROOT/'selection-routing-subcritical-covariance-review-r1.json')['ids']==[317413]
m=read(A/'byte-manifest.json');entries=m['files'];assert len(entries)==90
names=set()
for x in entries:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts and n not in names;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'byte-manifest.json','terminal_seal.receipt.json','terminal_seal.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==names|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==ready['frozen_bindings']==33
assert all(Path(n).is_relative_to(A) and sha(Path(n))==h for n,h in frozen.items())
before=read(A/'frozen-before.json');after=read(A/'frozen-after.json')
assert before['count']==after['count']==33 and before['mismatches']==after['mismatches']==[]
reservation=read(A/'reservation.json');assert reservation['ids']==[317413]
prov=read(A/'inputs/provenance317413.json');chunk=Path(prov['chunk'])
assert chunk.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
data=chunk.read_bytes();assert hashlib.sha256(data).hexdigest()==prov['chunk_sha256']
raw=data.splitlines(keepends=True)[prov['line']-1];obj=json.loads(raw)
assert raw==(A/'inputs/original317413.raw.jsonl').read_bytes() and hashlib.sha256(raw).hexdigest()==prov['raw_sha256'] and raw.endswith(b'\n') and obj['mathdb_id']==317413
tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1
assert tokens[0].decode()==prov['statement_token'] and hashlib.sha256(tokens[0]).hexdigest()==prov['statement_token_sha256'] and hashlib.sha256(obj['statement'].encode()).hexdigest()==prov['statement_utf8_sha256']
assert obj==read(A/'inputs/literal317413.json')==reservation['rows'][0]
family=read(A/'family-comparison.json');assert family['personally_compared']==len(family['comparisons'])==96
assert all(x['actual_fields'] and x['finding'] and x['comparison_to_317413'] for x in family['comparisons'])
source=read(A/'source-map.json')['317413'];assert sha(A/source['primary']['file'])==source['primary']['sha256']=='0573c9399b4a9598e3773b27403ca283275c9cf377438eb74d82eb36be20dd7e'
review=read(A/'review.json');assert review['317413']['decision']=='HOLD' and review['317413']['credit']==0
assert review['317413']['fresh_get_hops']==review['317413']['fresh_search_calls']==review['317413']['fresh_queries']==0
assert read(A/'search-budget.json')==dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True)
assert 'guard-ledger.jsonl' not in actual and 'search-charges.jsonl' not in actual
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q)
 assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 assert v['exit']==0 or (q.name=='scopes_middle_prior_a.receipt.json' and v['exit']==1)
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_seal.receipt.json')['exit']==0
summary='317413 independent all-fixed-index fourth-moment helper PASS and CONDITIONAL mixed-UI/polynomial bridge PASS retained as reviewer evidence, NOT full literal solution. Actual source AsN scaling/namedhatP2/degree/fixedc-versus-nearcritical conflicts leave named-polynomial binding unresolved; no root normalization choice or typography refutation. ROOT SCIENTIFIC_PARK: literal ordinary/source-final/prior/novelty/significance/formal gates unpaid, no formal dispatch. No matching public/routine exclusion authenticated. Reviewer personally compared96 trusted scopes with bounded nonmatch; actual source relevant pages/proofs/glyphs inspected, not whole manuscript. Specific source[9]martingale and[17]branching primary bodies unread. Entire original/final work remains closed by inheritedAIP403; no network request/search/charge used and inheriteddenial full read not completed, so future request must first read complete union.90ownmanifestfiles33frozen1corpusbinding96saved scopecomparisons verified; ordinary JSON-key diagnostic failure retained and repaired, material output recoveries/native-transient-writer unknowns disclosed. Helper/corrected-version/intendedendpoint one prospective family,credit0.'
record=dict(utc=now,source_lane=str(A),mathdb_id=317413,task_sha256=sha(A/'TASK.txt'),manifest_sha256=sha(A/'byte-manifest.json'),verified_manifest_files=90,verified_frozen_bindings=33,verified_original_bindings=[317413],verified_saved_scope_comparisons=96,review=review,source_map=source,runner_receipts=receipts,root_disposition='SCIENTIFIC_PARK_LITERAL_SOURCE_BINDING_UNPAID_NO_FORMAL_DISPATCH',scientific_summary=summary,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity, routing and credit adjudication only; no root mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r516.json');den['utc']=now;den['root_subcritical_covariance317413_review_scope']=summary
# All completed-packet integrity checks precede root integration/preparation writes.
save(P/'subcritical-covariance-source-parent-integration-r1.json',record);denpath=ROOT/'inherited-denials-r517.json';save(denpath,den)
base=read(ROOT/'r506-config.json')
base.update(number=507,protected_peers=['planar-laplacian-congruence-source-review-sol-r1','expanded-corpus-r506'],peer_routing_files=['selection-routing-planar-laplacian-review-r1.json','selection-routing-r506.json'],denials=str(denpath))
base['steering']+='\n'+summary+'\n';save(ROOT/'r507-config.json',base)
constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b'
assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);new=module.prepare(base)
for name in read(Path(new['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in base['protected_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'covariance-review-completion-boundary-delta.json',dict(utc=now,message=summary,new_protected_peer='expanded-corpus-r507',immutable_worker_inputs_unchanged=True,credit=0,accepted_new=57))
print(json.dumps(dict(files=90,frozen=33,corpus_bindings=1,scope_comparisons=96,receipts=len(receipts),ready=new,credit=0,accepted_new=57)))
