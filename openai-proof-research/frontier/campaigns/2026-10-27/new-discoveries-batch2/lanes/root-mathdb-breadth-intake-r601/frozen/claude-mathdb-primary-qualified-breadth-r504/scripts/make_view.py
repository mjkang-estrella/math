import json,sys
a=json.load(open(sys.argv[1],encoding='utf-8'))
o=open(sys.argv[2],'w',encoding='utf-8')
for i,x in enumerate(a,1):
    r=x['record']
    o.write('=== [%d] %s | %s:%d | %s\nTITLE: %s\nSRC: %s | %s | doc_by=%s %s | first=%s %s\nREFS: %s\nSTATEMENT:\n%s\n\n'%(i,r['mathdb_id'],x['chunk'],x['line'],r['post_type'],r['title'],r.get('source_name'),r.get('source_url'),r.get('documented_by_source_url'),r.get('documented_by_year'),r.get('first_stated_year'),r.get('first_stated_year_source_url'),json.dumps(r.get('references'),ensure_ascii=False)[:600],r['statement']))
