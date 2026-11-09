import json,sys
R=json.load(open(sys.argv[1]));a,b=int(sys.argv[2]),int(sys.argv[3])
for i,(k,v) in enumerate(R.items()):
    if not a<=i<b: continue
    r=v['record']
    print('=====',k,v['chunk'],v['line'],'|',r['title'])
    print('src:',r['source_name'],r['source_url'],'| doc:',r['documented_by_source_url'],r['documented_by_year'],'| first:',r['first_stated_year'],'| sol:',r['solution_count'],'| refs:',json.dumps(r['references'],ensure_ascii=False)[:300])
    print(r['statement'])
