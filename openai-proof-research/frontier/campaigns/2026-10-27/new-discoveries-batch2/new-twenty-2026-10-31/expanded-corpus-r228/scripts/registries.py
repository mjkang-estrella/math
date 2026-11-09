import pathlib,json,runpy,re
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
repos={'leanpool':'Vilin97/lean-pool','openai':'openai/math','omega':'the-omega-institute/trureturing'}
for k,repo in repos.items():
 h=json.loads((D/f'sources/{k}-head.json').read_text())['sha'];get(k+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{h}?recursive=1')
 p=D/f'sources/{k}-tree.json'
 if p.exists():
  o=json.loads(p.read_text());ps=[x['path'] for x in o.get('tree',[])];(D/f'sources/{k}-paths.txt').write_text('\n'.join(ps)+'\n');print(k,h,'truncated',o.get('truncated'))
  for x in ps:
   if re.search('paperfold|dyck|gimbert|cyclotomic|undomin|carnevale|odd.length|fibonacci|coil|gridding|flower.bouquet|mittleman|strongly.proper|non.permutation|subspace.ramsey|galvin|marmorino|expander|dirac|mazya|sum.product',x,re.I):print(x)
