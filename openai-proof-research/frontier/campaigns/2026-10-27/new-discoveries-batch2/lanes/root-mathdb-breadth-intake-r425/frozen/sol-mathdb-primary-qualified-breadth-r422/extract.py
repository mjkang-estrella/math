import pathlib,json,re,sys
O=pathlib.Path(__file__).parent; rows=[]
for r in json.loads((O/'selected-records.json').read_text()):
 p=O/'primary'/(r['source_url'].rsplit('/',1)[1]+'.txt')
 if not p.exists():continue
 pages=p.read_text().split('\f'); n=int(re.search(r'page (\d+)',r['references']).group(1)); text='\n'.join(pages[max(0,n-1):min(len(pages),n+1)])
 rows.append({'id':r['mathdb_id'],'file':str(p.relative_to(O)),'pdf_pages':[n,n+1],'excerpt':text})
(O/'primary-excerpts.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for x in rows:
 if int(sys.argv[1])<=x['id']<=int(sys.argv[2]):print('\nID',x['id'],'\n',x['excerpt'])
