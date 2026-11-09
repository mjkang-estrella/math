import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent
queries={'2308.06670':['AGX','independence number','\\lceil','v-1'], '2401.11496':['Conjecture','(1-n)','b-a'], '2407.07553':['Conjecture','conjecture','a+b'], '2408.03921':['Conjecture 4.','identity permutation','identity']}
out=[]
for e in json.loads((D/'derivative-bindings.json').read_text()):
 p=D/e['path'];b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];t=b.decode()
 for q in queries.get(e['path'].split('.')[0]+'.'+e['path'].split('.')[1],[]):
  start=0
  for i in range(3):
   k=t.find(q,start)
   if k<0:break
   s=t[max(0,k-350):k+2300];out.append({'file':p.name,'offset':max(0,k-350),'query':q,'text':s});print('\n',p.name,q,'offset',max(0,k-350),'\n',s);start=k+len(q)
(D/'selected-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
