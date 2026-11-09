from fetch import get
import json,pathlib,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];root=json.loads((D/'sources/omega-root.json').read_text())
for name in ['D5','Problems']:
 a=next(a for a in root['tree'] if a['path']==name)
 print(get(('omega-'+name+'.json',a['url']+'?recursive=1')),flush=True)
pat=re.compile(r'372498|372499|372532|372549|372593|372616|372618|372630|372631|372634|372658|372663|372684|372693|372705|372706|372713|372744|372759|372796|eventown|singular.*famil|even.?cycle|commutation|parking|normed.?flow|basis.?number|telic|admissib',re.I)
r=[]
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 x=json.loads(p.read_text());rows=x.get('tree',x) if isinstance(x,dict) else x
 if not isinstance(rows,list): print('shape',p,type(rows));continue
 matches=[a for a in rows if pat.search(str(a.get('path','')))]
 r.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),truncated=x.get('truncated') if isinstance(x,dict) else None,count=len(rows),matches=matches))
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
