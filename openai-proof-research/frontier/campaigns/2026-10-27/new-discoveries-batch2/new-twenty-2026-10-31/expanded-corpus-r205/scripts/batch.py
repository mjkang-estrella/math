import sys,pathlib,json,re,runpy,time
D=pathlib.Path(sys.argv[1]).resolve(); mode=sys.argv[2];sys.argv=sys.argv[:2];f=runpy.run_path(str(D/'scripts/fetch.py'));fetch=f['fetch']
if mode=='pdf':
 for i,o in json.loads((D/'extracted.json').read_text()).items():
  if 'arxiv' in o['source_url']:fetch(o['source_url'].replace('/abs/','/pdf/'),'pdf-'+i)
if mode=='extra':
 for label,url in [('zeck-proof','https://www.fq.math.ca/Papers/60-1/miller01152021.pdf'),('grundy-proof','https://arxiv.org/abs/2212.04565'),('grundy-refutation','https://hexagonmath.org/2610.00494v2')]:fetch(url,label)
if mode=='pool':
 h=json.loads((D/'sources/Vilin97-lean-pool-head/body').read_text())['sha'];t=json.loads((D/'sources/Vilin97-lean-pool-tree/body').read_text())
 for x in t['tree']:
  p=x['path']
  if p=='projects.yml' or (p.startswith('candidates/') and x['type']=='blob'):fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+h+'/'+p,'pool-'+p.replace('/','_'))
if mode=='search':
 for j,q in enumerate(['"2008.08503" lean','"1708.01329" lean','"Cameron Lucchini" lean','"taxicab" lean','"1702.03060" lean','"Grundy domination" lean','"matroid based valuation" lean','"Conlon Lee" lean']):
  fetch('https://api.github.com/search/repositories?q='+__import__('urllib.parse',fromlist=['quote']).quote(q),'github-query-'+str(j));time.sleep(8)
