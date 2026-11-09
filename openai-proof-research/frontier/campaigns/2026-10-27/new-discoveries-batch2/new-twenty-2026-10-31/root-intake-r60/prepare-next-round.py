"""Root documentary packet for the next discovery round on Claude Opus 5.5. Arguments: number prior_config denials peer1 peer2 note_file. Metadata only."""
import os,resource,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
num=int(sys.argv[1]);base=json.loads((ROOT/sys.argv[2]).read_text());den=sys.argv[3];active=sys.argv[4:6];note=Path(sys.argv[6]).read_text()
L=json.loads((P/'ledger.json').read_text());assert L['target_new']==80
hist='The user has barred GPT subagents for now. Every mention of GPT-6.1 Sol, Codex or Sol-only in inherited text, and the file name model-policy-sol-only.json, is historical and does not apply to you. No children or fallback.'
routing={f'selection-routing-r{n}.json' for n in range(525,num) if (ROOT/f'selection-routing-r{n}.json').exists()}|{x.name for x in ROOT.glob('selection-routing-*formal-r*.json')}|{x.name for x in ROOT.glob('selection-routing-qualification-*.json')}
completed={n for n in range(525,num) if (P/f'expanded-corpus-r{n}-parent-integration.json').exists()}
base.update(number=num,model='claude-opus-5-5',reasoning='high',service='default',model_line='THIS LANE RUNS ON CLAUDE OPUS 5.5, high effort. '+hist,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|completed),peer_routing_files=sorted(set(base['peer_routing_files'])|routing),denials=str(ROOT/den),steering=base['steering']+'\n'+note+'\n')
q=ROOT/f'r{num}-config.json';assert not q.exists()
C=Path(base['metadata_constructor']);spec=importlib.util.spec_from_file_location('discovery_models',C);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);q.write_text(json.dumps(base,indent=2)+'\n');r=m.prepare(base)
for name in json.loads((Path(r['lane'])/'historical-results-allowlist.json').read_text()):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
print(json.dumps({k:r[k] for k in ['lane','ids','task_sha256','active_peers','model','accepted_new']}))
