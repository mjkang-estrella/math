from pathlib import Path
import json,runpy,re
L=Path(__file__).resolve().parents[1];get=runpy.run_path(str(L/'scripts/http.py'))['get'];out={}
for k,repo,subs in [('omega','the-omega-institute/trureturing',['Problems']),('openai','openai/math',['preprints'])]:
 sha=json.loads((L/f'sources/{k}-head.json').read_text())['sha'];get(k+'-root-nonrecursive.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}')
 d=json.loads((L/f'sources/{k}-root-nonrecursive.json').read_text())
 for sub in subs:
  matches=[x for x in d.get('tree',[]) if x['path']==sub]
  if not matches:out[k+'-'+sub]={'error':'not in nonrecursive root','root_paths':[x['path'] for x in d.get('tree',[])]};continue
  key=k+'-'+sub+'-complete2.json';get(key,f'https://api.github.com/repos/{repo}/git/trees/{matches[0]["sha"]}?recursive=1');s=json.loads((L/'sources'/key).read_text());out[k+'-'+sub]={'truncated':s.get('truncated'),'paths':len(s.get('tree',[])),'hits':[x['path'] for x in s.get('tree',[]) if re.search('Eventown|Gonality|NeuralCode|Hyperconnectivity|RegularCharacter|CubicVertex|QMatroid|TriWeight|Jaeger|InfiniteHex|Carbonero|Ceria|TongViet|Muthiah|Laplacian.*Cograph|AlternatingRun',x['path'],re.I)]}
(L/'outputs/registry-final-supplement.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
