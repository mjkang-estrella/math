from fetch import *
import sys
x=json.loads((D/'extracted.json').read_text()); todo=[]
if sys.argv[1]=='0':todo=[('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]
urls=list(dict.fromkeys(o['source_url'].replace('/abs/','/pdf/') for o in x.values()))
for u in urls[int(sys.argv[1])*10:(int(sys.argv[1])+1)*10]:todo.append((u.split('/pdf/')[1].replace('/','_')+'.pdf',u))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,todo): print(v,flush=True)
