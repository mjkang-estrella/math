"""Root documentary packet for r534 on Claude Opus 5.5, structured-family ranking. Metadata only; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
L=json.loads((P/'ledger.json').read_text());assert L['accepted_new']==58 and L['target_new']==80
base=json.loads((ROOT/'r533-config.json').read_text());active=['regular-palm-locating-primary-qualification-claude-r1','expanded-corpus-r533']
note='\nResult 58 has been accepted: a conjecture for one structured infinite family after the general statement failed, solved by a small exact state summary, with a full Lean proof. 58/80 beyond 39 prior, 97 total.\n'
base.update(number=534,protected_peers=active,peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r533.json'}),denials=str(ROOT/'inherited-denials-r567.json'),steering=base['steering']+note)
q=ROOT/'r534-config.json';assert not q.exists();q.write_text(json.dumps(base,indent=2)+'\n')
C=Path(base['metadata_constructor']);spec=importlib.util.spec_from_file_location('discovery_models',C);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);r=m.prepare(base)
for name in json.loads((Path(r['lane'])/'historical-results-allowlist.json').read_text()):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
print(json.dumps({k:r[k] for k in ['lane','ids','task_sha256','active_peers','model','accepted_new']}))
