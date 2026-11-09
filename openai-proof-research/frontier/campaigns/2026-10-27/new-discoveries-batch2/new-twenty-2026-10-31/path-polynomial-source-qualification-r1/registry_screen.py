from pathlib import Path
import sys,json,re
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fetch_sources import P,get
R=P.parent/'expanded-corpus-r254';out=[]
pat=re.compile(r'331498|1312[.]4487|1510[.]00777|Kuszmaul|Bousquet|shuffle|QuarterPlane|Kreweras|PeakCount|UpperRight|[Ss]tack.*[Pp]arallel')
for n in ['openai-complete-preprints.body','openai-finalbranch-Combinatorics.body','openai-branch-Algebra.body','pool-tree.body','omega-current-Blueprint.body','omega-current-D5.body']:
 f=P/n if (P/n).exists() else R/n;d=json.loads(f.read_text());out.append({'file':str(f),'tree':d.get('sha'),'truncated':d.get('truncated'),'entries':len(d.get('tree',[])),'matches':[x for x in d.get('tree',[]) if pat.search(x['path'])]})
for f in sorted(R.glob('pool-index-*.body'))|set() if False else sorted(R.glob('pool-index-*.body')):
 s=f.read_text();out.append({'file':str(f),'matches':[l for l in s.splitlines() if pat.search(l)]})
f=R/'pool-projects.body';out.append({'file':str(f),'matches':[l for l in f.read_text().splitlines() if pat.search(l)]})
(P/'registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:12000])
head=json.loads((P/'omega-head.body').read_text())['sha']
for prefix in ['Blueprint','D5']:
 d=json.loads((P/('omega-current-'+prefix+'-changes.json')).read_text())
 for i,x in enumerate(d):
  if x['type']=='blob':get(('omega-newbody-'+prefix+'-'+str(i),'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+prefix+'/'+x['path']))
