# Render a read-only text view of assigned records (statement + source fields). Input bound before use.
import json,sys
R=json.load(open(sys.argv[1],encoding='utf-8'))
out=open(sys.argv[2],'w',encoding='utf-8')
for i,x in enumerate(R,1):
    r=x['record']
    out.write('=== [%d] %s | %s:%d | compl=%s | post=%s | year=%s | src=%s\n'%(i,r['mathdb_id'],x['chunk'][-10:],x['line'],r.get('statement_completeness'),r.get('post_type'),r.get('first_stated_year'),r.get('source_name')))
    out.write('TITLE: %s\nSRC_URL: %s\nDOC: %s\nREFS: %s\nSOLS: %s\n'%(r.get('title'),r.get('source_url'),r.get('documented_by_source_url'),json.dumps(r.get('references'),ensure_ascii=False)[:600],json.dumps(r.get('solutions'),ensure_ascii=False)[:300]))
    out.write('STATEMENT (%d chars):\n%s\n\n'%(x['statement_chars'],r.get('statement')))
