import json,pathlib,urllib.request,concurrent.futures
base=pathlib.Path(__file__).parent
items={x['number']:x for p in (base.parent/'twenty-proof-campaign/queued-sources').glob('*-list.json') for x in json.load(open(p))['items']}
nums=[378626,372794,405260,350342,371791,371324,374660,374661,374662,374663,374664,374665,374666,364540,352508,338823,338822,349070,344949,344948,344947,337932,343909,358561,370181,327048,382158,319089,336624,405533,372393]
def get(n):
 p=base/'sources'/f'{n}.json'
 try:
  if not p.exists():
   req=urllib.request.Request('https://mathdb.com/api/posts/'+items[n]['id'],headers={'User-Agent':'Mozilla/5.0'})
   p.write_bytes(urllib.request.urlopen(req,timeout=50).read())
  d=json.load(open(p)); return str(n)+' '+str(d)[:120]
 except Exception as e:return str(n)+' ERROR '+str(e)
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
 for s in ex.map(get,nums): print(s)
