import pathlib,json,re,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
terms=['Steiner','Tropical','DotProduct','SequenceSaturation','Kanungo','TotalCut','BeckFiala','Barnette','Benzel','ColoredPartition','FIgraph','Transchromatic','FlowReconfiguration','KangNikiforov','Umans','AlternativeDivision']
out={}
for name in ['D5','Problems']:
 p=L/f'sources/omega-{name}-tree.json';d=json.loads(p.read_text())
 paths=[x['path'] for x in d['tree'] if x['type']=='blob']
 out[name]={'truncated':d.get('truncated'),'blob_count':len(paths),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':{t:[s for s in paths if t.lower() in s.lower()] for t in terms}}
r=json.loads((L/'outputs/registry-screen.json').read_text());r['omega_current_path_screen']=out
r['limitations'][1]='Omega current D5/Problems path trees screened (not all bodies); OpenAI HEAD matches cached campaign scope, not a new all-file audit.'
(L/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2))
print(json.dumps(out,indent=2))
