"""Root documentary packet for r536 on Claude Opus 5.5, structured-family ranking. Metadata only; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
L=json.loads((P/'ledger.json').read_text());assert L['accepted_new']==58 and L['target_new']==80
base=json.loads((ROOT/'r535-config.json').read_text());active=['zeckendorf-games-formal-deepseek-r1','biharmonic-tree-primary-qualification-claude-r1']
hist='The user has barred GPT subagents for now. Every mention of GPT-6.1 Sol, Codex or Sol-only in inherited text, and the file name model-policy-sol-only.json, is historical and does not apply to you. No children or fallback.'
note='\n'+json.loads((P/'expanded-corpus-r535-parent-integration.json').read_text())['scientific_summary']+'\nRecent qualification outcomes: 344875, 368315 and 342017 were correct and excluded as routine: a re-indexed source count with an optimized allocation, a complete reduction to classical order-ideal rowmotion, and a literal statement with a one-page proof from a source lemma. Test your candidate against all three patterns, and against general theory of the object, before proposing it.\n'
base.update(number=536,model='claude-opus-5-5',reasoning='high',service='default',model_line='THIS LANE RUNS ON CLAUDE OPUS 5.5, high effort. '+hist,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{533,534,535}),peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r535.json','selection-routing-zeckendorf-formal-r1.json','selection-routing-qualification-352303.json','selection-routing-qualification-342017.json','selection-routing-qualification-368315.json'}),denials=str(ROOT/'inherited-denials-r574.json'),steering=base['steering']+note)
q=ROOT/'r536-config.json';assert not q.exists();q.write_text(json.dumps(base,indent=2)+'\n')
C=Path(base['metadata_constructor']);spec=importlib.util.spec_from_file_location('discovery_models',C);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);r=m.prepare(base)
for name in json.loads((Path(r['lane'])/'historical-results-allowlist.json').read_text()):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
print(json.dumps({k:r[k] for k in ['lane','ids','task_sha256','active_peers','model','accepted_new']}))
