import pathlib,sys,json,time,urllib.parse,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
p=D/'outputs/registry-screen.json';out=json.loads(p.read_text())
queries=['"Bruhat" "orbit" lean','"2410.04611" lean','"hard squares" lean','"Panyushev" "duality" lean','"symplectic" "content" lean','"2503.08285" lean','"Speyer" "planar" lean','"quadrangulation" lean']
for q in queries:
 z=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search');out['queries'].append({'query':q,'receipt':z,'hits':json.loads(pathlib.Path(z['body']).read_text()).get('items',[]) if z.get('status')==200 else []});p.write_text(json.dumps(out,indent=2))
 print(q,z['status'],flush=True)
 if z.get('status')!=200:break
 time.sleep(8)
terms=['381151','322999','323000','323625','367923','349324','328588','373846','374680','375694','367479','368974','363775','365147','358955','354073','354340','354633','354634','356182','panyushev','bruhat','zcurve','z-curve','symplectic','hard.square','popstack','speyer','quadrangulation','boone','uncu','kanade','signed.path','circle.pattern','extremal.prime','pons','batle']
pat=re.compile('|'.join(terms),re.I);matches=[]
for r in out['receipts']:
 if r.get('status')!=200:continue
 s=pathlib.Path(r['body']).read_text()
 for l in s.splitlines():
  if pat.search(l):matches.append({'url':r['url'],'line':l[:1200]})
(D/'outputs/registry-matches.json').write_text(json.dumps(matches,indent=2));print('matches',len(matches))
