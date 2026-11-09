import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent
s=(L/'fetch_sources.py').read_text().split('items=[]')[0];g={'__file__':str(L/'fetch_sources.py')};exec(compile(s,str(L/'fetch_sources.py'),'exec'),g)
head=re.findall(r'"oid":"([0-9a-f]{40})"',(L/'sources/omega-head.html').read_text())[0]
jobs=[('swanepoel-publisher.pdf','https://www.ams.org/tran/2016-368-10/S0002-9947-2014-06601-3/S0002-9947-2014-06601-3.pdf'),('riegler-journal.pdf','https://dmtcs.episciences.org/2331/pdf'),('openai-CONTENTS-current.md','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md')]
d=json.loads((L.parent/'path-polynomial-source-qualification-r1/omega-current-D5.body').read_text())
for x in d['tree']:
 if re.search(r'ToleranceNonGroup|BenefitMarginalToleranceSharp|JointBenefitToleranceSharp|PrimeGap186ComponentTolerance',x['path']):jobs.append(('omega-'+x['path'].split('/')[-1],'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/D5/'+x['path']))
with g['concurrent'].futures.ThreadPoolExecutor(max_workers=2) as e:list(e.map(g['fetch'],jobs))
