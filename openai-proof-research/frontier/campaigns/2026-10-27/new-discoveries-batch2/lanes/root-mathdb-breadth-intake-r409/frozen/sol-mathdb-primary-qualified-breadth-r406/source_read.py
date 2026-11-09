import json,pathlib,re
L=pathlib.Path(__file__).parent;t=(L/'primary/hayman.txt').read_text();out=[]
for x in json.loads((L/'selected-records.json').read_text()):
 r=x['record']
 if '1809.07200' not in r['source_url']:continue
 n=r['title'].split('Problem ')[1];m=re.search(r'Problem '+re.escape(n)+r'\b',t);assert m
 end=re.search(r'\nProblem \d+\.\d+\b',t[m.end():]);s=t[m.start():m.end()+end.start() if end else len(t)]
 out.append({'mathdb_id':r['mathdb_id'],'label':n,'start_line':t[:m.start()].count('\n')+1,'body':s});print('\nID',r['mathdb_id'],s)
(L/'primary/hayman-assigned-excerpts.json').write_text(json.dumps(out,indent=2)+'\n')
