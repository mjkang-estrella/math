import json,sys
for p in sys.argv[1:]:
    d=json.load(open(p))
    items=d['results'] if 'results' in d else [d]
    print('==',p,'count',d.get('meta',{}).get('count'))
    for w in items:
        print(w.get('id'),'|',w.get('doi'),'|',w.get('publication_date'),'|',(w.get('title') or '')[:120],'| cited_by',w.get('cited_by_count'),'|',', '.join(a['author']['display_name'] for a in w.get('authorships',[])[:4]))
