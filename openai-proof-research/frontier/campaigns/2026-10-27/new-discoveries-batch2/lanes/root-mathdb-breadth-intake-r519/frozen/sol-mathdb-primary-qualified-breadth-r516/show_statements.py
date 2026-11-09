import json,pathlib,hashlib
O=pathlib.Path(__file__).resolve().parent
rows=json.loads((O/'records.json').read_text()); out=[]
for x in rows:
 r=x['record'];s=r['statement'];out.append({**{k:x[k] for k in ['mathdb_id','chunk','line','canonical_record_sha256']},'statement':s,'statement_sha256':hashlib.sha256(s.encode()).hexdigest(),'statement_utf8_size':len(s.encode()),'source_url':r['source_url'],'source_name':r['source_name'],'references':r['references']})
(O/'statements.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for i,x in enumerate(out):
 if int(__import__('sys').argv[1])<=i<int(__import__('sys').argv[2]):print('\nINDEX',i,'ID',x['mathdb_id'],'SOURCE',x['source_url'],'\n',x['statement'],'\nREFERENCES',x['references'])
