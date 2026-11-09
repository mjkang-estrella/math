import pathlib,json,subprocess,sys,re
D=pathlib.Path(__file__).resolve().parents[1];J=json.loads((D/'sources/omega-root.json').read_text());a=next(x for x in J['tree'] if x['path']=='Problems');subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),'omega-Problems.json',a['url']+'?recursive=1'])
rows=json.loads((D/'extracted.json').read_text());terms=[str(i) for i in rows]+[o['source_url'].split('/')[-1] for o in rows.values()]+['SimplicialTree','Dewdney','Perarnau','Petersen','Heawood','Rivezzi','Vlasev','Bressoud','Kanade','Orlik','Kirgizov','Lewis','SupportRigidity','Parabolic','Antidiagonal','GenusRange','StronglyAperiodic','InversionStatistic','JohnsonStatistic']
out={}
for reg in ['pool-LeanPool_projects.yml','pool-candidates_discovered.yml','pool-candidates_README.md','pool-candidates_shortlist.md','pool-candidates_provenance.md']:
 lines=(D/'sources'/reg).read_text().splitlines();out[reg]={t:[{'line':i,'text':l} for i,l in enumerate(lines,1) if t.casefold() in l.casefold()] for t in terms};out[reg]={k:v for k,v in out[reg].items() if v}
for reg in ['omega-D5.json','omega-Problems.json']:
 j=json.loads((D/'sources'/reg).read_text());out[reg]={'truncated':j['truncated'],'sha':j['sha'],'hits':{t:[x['path'] for x in j['tree'] if t.casefold() in x['path'].casefold()] for t in terms}};out[reg]['hits']={k:v for k,v in out[reg]['hits'].items() if v}
(D/'outputs/registry-detailed.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2)[:8000])
