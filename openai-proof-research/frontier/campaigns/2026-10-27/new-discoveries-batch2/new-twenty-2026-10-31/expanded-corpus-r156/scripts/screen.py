import pathlib,json,re,hashlib
p=pathlib.Path.cwd();R=json.loads((p/'reservation.json').read_text());out=[]
for row in R['rows']:
 i=row['mathdb_id'];text=(p/'sources'/f'{i}.txt').read_text();lines=text.splitlines();hits=[]
 for j,l in enumerate(lines):
  if re.search('Conjecture|conjecture|computational|checked|verified',l):hits.append({'line':j+1,'text':' '.join(lines[max(0,j-1):j+3])[:2600]})
 out.append({'id':i,'excerpts':hits})
(p/'outputs/source-excerpts.json').write_text(json.dumps(out,indent=2))
for o in out:
 print('\nID',o['id'])
 for h in o['excerpts'][:8]:print(h['line'],h['text'][:900])
for key in ['openai-head','omega-head']:
 d=json.loads((p/'sources'/f'{key}.html').read_text());print(key,d['sha'])
