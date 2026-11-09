"""Root documentary packet for one discovery round toward 80. Metadata only; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,sys,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
number=int(sys.argv[1]);selname=sys.argv[2];other=int(sys.argv[3])
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
base=json.loads((ROOT/'r524-config.json').read_text());C=ROOT/'prepare_discovery_packet_target80.py'
S=ROOT/selname
extra='selection-routing-r525.json' if number==526 else None
routing=base['peer_routing_files']+['selection-routing-r524.json','selection-routing-parking-qualification-r2.json','selection-routing-lean-diagnostic-r1.json']+([extra] if extra else [])
broad=number==526
note='\nUSER DECISIONS 2026-11-08, binding. Target is now 80 new accepted results beyond 39 prior; 57/80, 96 total. 323531 is excluded by user ruling, credit 0, and its 2014 and 2017 final versions stay closed. 338806 stays on scientific hold. r523, r524 and the focused finite lane are complete with no credit. Recent results: 350767, 341690, 362896 and 336276 all reached full proofs and were then excluded as routine, because a short generic argument or a source reduction made the target an instance. Before you propose any candidate, try seriously to find that argument yourself: a generic proof, a one-parameter family containing the target, or a complete reduction to a source theorem. Report the outcome. A full proof that survives this attempt is what the campaign needs. Do not run Lean in this lane; Lean feasibility is being re-tested separately after an address-space change, and an algebraic or complex-number endpoint should no longer be treated as disqualifying on the kernel-check wall alone.\n'
if broad:note+='This round draws from elementary number theory and finite algebra rather than the usual discrete tags, because twelve straight rounds in the discrete pool produced no credit. The substantive credit standard is unchanged.\n'
base.update(number=number,protected_peers=['lean-address-space-diagnostic-sol-r1',f'expanded-corpus-r{other}'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{523,524}),peer_routing_files=routing,denials=str(ROOT/'inherited-denials-r556.json'),excluded_ids=sorted(set(base['excluded_ids'])|{348662,364538,358527}),metadata_constructor=str(C),metadata_selector=str(S),metadata_selector_sha256=sha(S),steering=base['steering']+note)
cfg=ROOT/f'r{number}-config.json';assert not cfg.exists();cfg.write_text(json.dumps(base,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('discovery_target80',C);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);r=m.prepare(base)
for name in json.loads((Path(r['lane'])/'historical-results-allowlist.json').read_text()):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
print(json.dumps({k:r[k] for k in ['lane','ids','task_sha256','active_peers','target_new']}))
