import json,sys,re
R=json.load(open(sys.argv[1]));seen=[]
for k,v in R.items():
    m=re.search(r'arxiv\.org/abs/([0-9.]+)',v['record']['source_url']);a=m.group(1)
    if a not in seen: seen.append(a)
print(' '.join(seen))
