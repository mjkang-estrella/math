exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=json.loads')[0])
import re
urls={}
for f in (l/'sources').glob('*-abs'):
 a=f.name[:-4];vs=sorted(set(map(int,re.findall(r'/abs/[0-9.]+v(\d+)',f.read_text()))))
 for v in vs[:-1]:urls[a+'v'+str(v)+'-pdf']='https://arxiv.org/pdf/'+a+'v'+str(v)
repos={'openai':'openai/math','omega':'the-omega-institute/trureturing','aim':'MColbrook/AIM','pool':'Vilin97/lean-pool'};heads={}
for name,repo in repos.items():
 s=(l/'sources'/(name+'-head')).read_text();h=re.search(r'currentOid.{0,6}([a-f0-9]{40})',s).group(1);heads[name]={'repo':repo,'head':h};urls[name+'-commit']='https://github.com/'+repo+'/commit/'+h
 for path in {'openai':['CONTENTS.md'],'omega':['README.md','Trureturing.lean'],'aim':['README.md'],'pool':['LeanPool.lean','LeanPool/projects.yml']}[name]:urls[name+'-'+path.replace('/','_')]='https://raw.githubusercontent.com/'+repo+'/'+h+'/'+path
(l/'registry-heads.json').write_text(json.dumps(heads,indent=2));(l/'fetch-more.json').write_text(json.dumps(urls,indent=2))
