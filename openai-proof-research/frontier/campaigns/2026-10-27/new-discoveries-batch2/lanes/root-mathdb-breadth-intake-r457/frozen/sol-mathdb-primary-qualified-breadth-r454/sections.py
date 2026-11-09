import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent;out=[]
for x in json.loads((L/'assigned-records.json').read_text()):
 r=x['record'];p=L/'sources'/(r['source_url'].split('/')[-1]+'.txt')
 if not p.exists():continue
 pages=p.read_text().split('\f');n=int(re.search('page (\d+)',r['source_name'])[1]);s='\n'.join(pages[max(0,n-2):n+1]);out.append(dict(id=r['mathdb_id'],source=r['source_url'],page=n,passage=s))
(L/'primary-sections.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print('sections',len(out))
for x in out:
 if x['id'] in [404452,404570,404620,404726,404789,404790,404801,404890,404901,404902,404955]:print('\nID',x['id'],'\n',x['passage'])
