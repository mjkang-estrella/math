"""Root documentary packet for one discovery round on Claude or DeepSeek. Metadata only; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,sys,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
number=int(sys.argv[1]);kind=sys.argv[2];other=int(sys.argv[3]);priorcfg=sys.argv[4]
base=json.loads((ROOT/priorcfg).read_text());C=ROOT/'prepare_discovery_packet_models.py'
hist='The user has barred GPT subagents for now. Every mention of GPT-6.1 Sol, Codex or Sol-only in inherited text, and the file name model-policy-sol-only.json, is historical and does not apply to you. No children or fallback.'
if kind=='claude':cfg=dict(model='claude-opus-5-5',reasoning='high',service='default',model_line='THIS LANE RUNS ON CLAUDE OPUS 5.5, high effort. '+hist)
else:cfg=dict(model='spark/DeepSeek-V4.1-Flash-1017',reasoning='high',service='default',model_line='THIS LANE RUNS ON PI DEEPSEEK V4.1 FLASH, high thinking. '+hist+' If your environment has no native web search tool, say so at handback, do not charge the search budget, and rely on guarded GETs of source URLs; prior-art status for any candidate then stays explicitly unpaid.')
extra=[] if number!=531 else ['selection-routing-r530.json']
ann=json.loads((P/'expanded-corpus-r529-parent-integration.json').read_text())['scientific_summary']
note='' if number==531 else '\n'+json.loads((P/'expanded-corpus-r528-parent-integration.json').read_text())['scientific_summary']+'\n'+ann+'\n'
base.update(cfg,number=number,protected_peers=['transitive-bunkbed-reach-formal-deepseek-r20',f'expanded-corpus-r{other}'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{528,529}),peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r529.json','selection-routing-bunkbed-dominance-r22.json'}|set(extra)),denials=str(ROOT/'inherited-denials-r563.json'),metadata_constructor=str(C),steering=base['steering']+note)
q=ROOT/f'r{number}-config.json';assert not q.exists();q.write_text(json.dumps(base,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('discovery_models',C);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);r=m.prepare(base)
for name in json.loads((Path(r['lane'])/'historical-results-allowlist.json').read_text()):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
print(json.dumps({k:r[k] for k in ['lane','ids','task_sha256','active_peers','target_new','model']}))
