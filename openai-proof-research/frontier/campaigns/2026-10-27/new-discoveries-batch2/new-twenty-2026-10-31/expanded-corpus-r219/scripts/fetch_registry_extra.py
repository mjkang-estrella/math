import sys,json,pathlib,urllib.parse,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch_http import get
D=pathlib.Path(__file__).resolve().parents[1];sha=json.loads((D/'http/leanpool-head.json').read_text())['sha']
for p in ['LeanPool/projects.yml','candidates/discovered.yml','candidates/decisions.jsonl','candidates/manual.txt','candidates/shortlist.md','candidates/provenance.jsonl']:
 get('lp-'+p.replace('/','-'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}')
for i,q in enumerate(['"2606.24016" lean','"2606.25493" lean','"2607.00153" lean','"2607.26606" lean','"K4" "rigidity" lean','"Ellis Keller Lifshitz" lean']):
 r=get(f'github-search-{i}.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
 if r.get('status') in [403,429]:break
 time.sleep(8)
