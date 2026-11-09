import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent;out=[]
for x in json.loads((L/'assigned-records.json').read_text()):
 r=x['record'];p=L/'sources'/('ems-'+r['source_url'].rsplit('/',1)[1]+'.txt');n=int(re.search('page (\d+)',r['source_name'])[1]);pages=p.read_text().split('\f') if p.exists() else []
 text=pages[n-1] if len(pages)>=n else ''
 out.append({'mathdb_id':r['mathdb_id'],'file':str(p.relative_to(L)),'pdf_page':n,'text':text,'context_previous':pages[n-2] if n>1 and len(pages)>=n else '', 'context_next':pages[n] if len(pages)>n else ''})
(L/'primary-sections.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for a in out:print('\nID',a['mathdb_id'],'PAGE',a['pdf_page'],'\n',a['text'])
