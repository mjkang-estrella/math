"""Targeted resume after a metadata-pool assertion; existing review stays frozen."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
assert not (P/'expanded-corpus-r467').exists() and not (P/'expanded-corpus-r468').exists()
review=json.loads((ROOT/'percolation-review-r1-ready.json').read_text());R=Path(review['lane'])
assert sha(R/'TASK.txt')==review['task_sha256'] and not (R/'bootstrap-receipt.json').exists()
assert all(sha(Path(n))==h for n,h in json.loads((R/'frozen-inputs.json').read_text()).items())
config=json.loads((ROOT/'r467-config.json').read_text())
old_config=dict(config)
config.update(year_floor=2000,candidate_pool=400)
config['steering']+='\nMETADATA ROUTING EXPANSION: the unreserved finite/discrete metadata pool with year floor2012 has only13 records under the existing soft/hard filters; this is NOT full technical corpus review or a novelty conclusion. Root broadened year floor to2000, yielding619 offline metadata candidates before assignment. Exact twenty originals, disjointness, all prior reservations and source/qualification requirements are unchanged. Older questions may be already public or hard; read actual statements/proofs rather than assuming eligibility from age or an open label.\n'
save(ROOT/'r467-year-routing-recovery.json',dict(before=old_config,after=config,reason='Both120and400 pool attempts failed before discovery directory creation because actual2012finitepool is13; capped metadata diagnostic found619at2000 and764at1900, no mathematics or network. Review frozen25 remains unchanged.'))
(ROOT/'r467-config.json').write_text(json.dumps(config,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
ready=[module.prepare(config)]
config468=dict(config);config468.update(number=468,protected_peers=['expanded-corpus-r467',R.name],peer_routing_files=['selection-routing-percolation-review-r1.json','selection-routing-r467.json'])
save(ROOT/'r468-config.json',config468);ready.append(module.prepare(config468))
for item in ready:
 allow=json.loads((Path(item['lane'])/'historical-results-allowlist.json').read_text())
 forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
 assert all(not any(token in part.lower() for token in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
 assert all('expanded-corpus-r463' not in name and 'expanded-corpus-r466' not in name for name in allow)
assert not set(ready[0]['ids'])&set(ready[1]['ids'])
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
save(ROOT/'history-flat-boundary-fix-20261108.json',dict(utc=now,preparation_helper_sha256=sha(ROOT/'prepare_discovery_packet.py'),actual_failure='r463 andr466 protected flat history integrations opened despite completed allowlisting',fix='Filter every relativepathcomponent including flatbasename BEFOREstat/open/hash; filter root parent-integration collection similarly; exclude quarantined histories/parents',verified_new_history_allowlists=[dict(lane=x['lane'],sha256=sha(Path(x['lane'])/'historical-results-allowlist.json'),no_protected_component=True,no_quarantined_history=True) for x in ready],old_frozen_helpers_modified=False,old_quarantine_waived=False,root_external_protected_paths_followed=False,metadata_preparation_recovery='Both120and400 offline pool attempts failed exact20 assertion BEFORE either discovery directory existed. Diagnostic found only13finiteunreservedmetadata records at2012,619at2000. Review frozen25 remains unchanged. Targeted resume usesyear2000and400offlinecandidates, exact20disjointassignments; no network/search/cap budget changed. Both failed invocations preserved in tool history, rootbefore/after config saved separately.'))
print(json.dumps(dict(accepted_new=57,review=review,discovery=ready,history_filter_checks='Both actual new allowlists exclude every protected component and quarantined history; old frozen files unchanged',offline_candidate_pool=400,year_floor=2000)))
