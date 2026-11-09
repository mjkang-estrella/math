import urllib.request,json,pathlib,concurrent.futures,sys
P=pathlib.Path(__file__).parent
index={a['number']:a for p in P.glob('*.json') for a in json.loads(p.read_text()).get('items',[])}
def get(n):
 a=index[int(n)];u='https://mathdb.com/api/posts/'+a['id']
 d=json.load(urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0','Accept':'application/json'})));(P/(str(n)+'.json')).write_text(json.dumps(d,indent=2));print(n,json.dumps(d,ensure_ascii=False)[:16000])
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:list(ex.map(get,sys.argv[1:]))
