import pathlib,json,urllib.request,hashlib,datetime,re
p=pathlib.Path(__file__).parent;r=json.loads((p/'http.json').read_text())
def get(name,url):
 x={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:b=f.read();x.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  (p/'sources'/name).write_bytes(b);r.append(x);return b
 except Exception as e:x['error']=str(e);r.append(x);return b''
get('machina.html','https://lean.up.railway.app/')
head=json.loads((p/'sources/omega-head.json').read_text())['sha']
get('omega-delta.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/23a4ae6f843d1635869b7656fb6bd681121447a8...'+head)
base=p.parent/'root-edge-irregulator-final-freeze-r1'
hits=[]
for n in ['omega-tree.txt','openai-tree.txt']:
 for line in (base/n).read_text().splitlines():
  if re.search(r'LCM|GCD|Motzkin|Subtraction|LogConcav|LogConvex',line,re.I):hits.append({'tree':n,'line':line})
(p/'registry-hits.json').write_text(json.dumps(hits,indent=2))
(p/'http.json').write_text(json.dumps(r,indent=2))
print('HEAD',head,'OpenAI',json.loads((p/'sources/openai-head.json').read_text())['sha']);print((p/'sources/machina.html').read_text()[-1500:]);print('delta file count',len(json.loads((p/'sources/omega-delta.json').read_text()).get('files',[])))
