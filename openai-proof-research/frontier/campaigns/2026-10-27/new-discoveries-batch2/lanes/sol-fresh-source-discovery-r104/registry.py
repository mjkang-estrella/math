import sys
sys.argv.append('registry')
from research import P,get,sha
import json,re,urllib.parse,datetime
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limits':'Inherited complete 18:13 path inventory plus dated deltas; not global semantic coverage. Earlier aggregate compare300 cap unresolved.'}
pat=re.compile('Evolution|Quandle|Barei|Kaygorodov|Idempotent|Peirce|Nilpoten',re.I)
for key,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 d=json.loads((P/'sources'/f'{key}-head.json').read_text());h=d['sha'];out[key]={'head':h,'author':d['commit']['author'],'committer':d['commit']['committer']}
 base=P.parent/'root-edge-irregulator-final-freeze-r1'/f'{key}-tree.txt';matches=[l.strip().split('\t')[-1] for l in base.open() if pat.search(l)];out[key].update(baseline_sha256=sha(base.read_bytes()),matches=matches)
 # Restrict actual body selection to relevant algebra families, not generic idempotent topology.
 selected=[s for s in matches if re.search('Evolution|Quandle|Barei|Peirce',s,re.I) and s.endswith(('.md','.lean'))];out[key]['selected']=selected
 for i,path in enumerate(selected):get(f'{key}-body-{i}.txt',f'https://raw.githubusercontent.com/{repo}/{h}/'+urllib.parse.quote(path))
 if key=='omega':
  b=get('omega-delta.json',f'https://api.github.com/repos/{repo}/compare/73a5033dd654a16a14fcd1b13277f1a03d81d826...{h}')
  if b:
   delta=json.loads(b);out[key]['delta']={'base':'73a5033dd654a16a14fcd1b13277f1a03d81d826','commits':delta.get('total_commits'),'files':len(delta.get('files',[])),'possibly_capped':len(delta.get('files',[]))>=300,'paths':[f['filename'] for f in delta.get('files',[])]}
   for i,f in enumerate(delta.get('files',[])):
    if f['status']!='removed':get(f'omega-delta-{i}.txt',f'https://raw.githubusercontent.com/{repo}/{h}/'+urllib.parse.quote(f['filename']))
(P/'registry.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
