import urllib.request,urllib.error,pathlib,json,hashlib,datetime,concurrent.futures
D=pathlib.Path(__file__).resolve().parents[1]
items=[('source.pdf','https://cs.du.edu/~petr/data/papers/Moufang_loops_that_share_associator.pdf'),('journals.html','https://cs.du.edu/~petr/in_research_journals.html'),('loops.html','https://gap-packages.github.io/loops/doc/chap7_mj.html'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('classification.pdf','https://www.cs.du.edu/~petr/data/papers/toward_the_classification_of_Moufang_loops_of_order_64.pdf'),('code.pdf','https://cs.du.edu/~petr/data/papers/code_loops_in_dimension_at_most_8.pdf'),('closest.pdf','https://cs.du.edu/~petr/data/papers/closest_multiplication_tables_of_groups.pdf')]
def get(item):
 name,url=item;r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathDB-independent-review/1.0'}),timeout=25) as f:
   data=f.read();r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(D/'sources'/name).write_bytes(data)
 except Exception as e:r['error']=str(e)
 (D/'receipts'/(name+'.json')).write_text(json.dumps(r,indent=2));print(r,flush=True)
if __name__ == '__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(get,items))
