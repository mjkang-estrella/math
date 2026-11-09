exec((__import__('pathlib').Path(__file__).parent/'setup.py').read_text().split('rows=[]')[0])
# Correct the administrative basename collision in setup; retain both snapshots.
shutil.copyfile(B/'AGENTS.md',L/'administrative/batch-AGENTS.md')
shutil.copyfile(B.parents[3]/'AGENTS.md',L/'administrative/ancestor-AGENTS.md')
for name in ['ledger.json','prior-campaign-context.json']:
 obj=json.loads((L/'administrative'/name).read_text());print(name,'top keys',list(obj))
 print('target mentions',[(m.start(),str(obj)[max(0,m.start()-100):m.start()+400]) for m in __import__('re').finditer('Bani|Elez|17046',str(obj))][:15])
rows=json.loads((L/'bindings.json').read_text())
for p in [C/'primary/2610.13366.pdf',C/'texts/2610.13366.txt',pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json'),pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]:
 a=h(p);q=L/'science'/(a[:16]+'-'+p.name);shutil.copyfile(p,q);q.chmod(0o444);assert a==h(p)==h(q);rows.append(dict(original=str(p),copy=str(q),sha256=a))
(L/'bindings.json').write_text(json.dumps(rows,indent=2))
import re
for name in ['target','author','title']:
 html=(L/'live'/(name+'.html')).read_text();txt=(L/'live'/(name+'.txt')).read_text()
 print(name,'ids',list(dict.fromkeys(re.findall(r'arxiv.org/abs/([\d.v]+)',html))))
 if name=='target':print(txt[txt.find('Submission history'):txt.find('Submission history')+650])
 if name=='title':print(txt[:9000])
