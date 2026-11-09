from pathlib import Path
import json,runpy,re,hashlib,subprocess
L=Path(__file__).resolve().parents[1];get=runpy.run_path(str(L/'scripts/http.py'))['get'];out={}
for k,repo,subs in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 d=json.loads((L/f'sources/{k}-tree.json').read_text())
 for sub in subs:
  matches=[x for x in d['tree'] if x['path']==sub]
  if not matches:out[k+'-'+sub]={'error':'not in truncated root'};continue
  sha=matches[0]['sha'];key=k+'-'+sub+'-complete.json';get(key,f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1');s=json.loads((L/'sources'/key).read_text());hits=[x['path'] for x in s.get('tree',[]) if re.search(r'Eventown|Gonality|NeuralCode|Hyperconnectivity|RegularCharacter|CubicVertex|QMatroid|TriWeight|Jaeger|InfiniteHex|Carbonero|Ceria|TongViet|Muthiah|Laplacian.*Cograph|AlternatingRun',x['path'],re.I)];out[k+'-'+sub]={'truncated':s.get('truncated'),'paths':len(s.get('tree',[])),'hits':hits}
(L/'outputs/registry-complete-supplement.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
ids=json.loads((L/'reservation.json').read_text())['ids'];pat=r'(?<![0-9a-z])('+('|'.join(map(str,ids)))+r')(?![0-9a-z])'
r=subprocess.run(['rg','-n','-i','-P',pat,str(L.parent.parent.parent),'-g','SUMMARY.md','-g','CANDIDATE.md','-g','results.json','-g','ledger.json','-g','prior-campaign-context.json'],capture_output=True,text=True)
lines=[x for x in r.stdout.splitlines() if str(L) not in x];(L/'outputs/historical-id-screen.txt').write_text('\n'.join(lines));print('history matches',len(lines))
