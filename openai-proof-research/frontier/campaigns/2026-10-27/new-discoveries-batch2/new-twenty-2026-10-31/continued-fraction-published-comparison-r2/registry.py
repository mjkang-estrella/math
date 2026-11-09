from pathlib import Path
import json,subprocess,sys,re
r=Path(__file__).parent; head=json.loads((r/'omega-head.body').read_text())['sha']; tree=json.loads((r/'omega-d5.body').read_text()); hits=[x for x in tree['tree'] if x['type']=='blob' and x['path'].startswith('S1/Depth/ContinuedFractions/')]; (r/'relevant-subtree.json').write_text(json.dumps(hits,indent=2))
args=[]
for x in hits: args += [Path(x['path']).stem,'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/D5/'+x['path']]
args+=['cf-history','https://api.github.com/repos/the-omega-institute/trureturing/commits?sha='+head+'&path=D5/S1/Depth/ContinuedFractions&per_page=100','bound-history','https://api.github.com/repos/the-omega-institute/trureturing/commits?sha='+head+'&path=D5/S1/Depth/ContinuedFractions/CompleteQuotientBound.lean&per_page=100']
subprocess.run([sys.executable,str(r/'fetch.py')]+args,check=True,timeout=180)
print('SUBTREE',len(hits))
