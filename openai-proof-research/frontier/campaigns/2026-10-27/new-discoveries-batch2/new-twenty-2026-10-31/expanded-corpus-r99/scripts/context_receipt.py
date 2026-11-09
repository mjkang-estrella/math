import pathlib,json,hashlib,re
L=pathlib.Path.cwd();B=L.parent.parent;ids=set(json.loads((L/'reservation.json').read_text())['ids']);out={}
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 j=json.loads(p.read_text());out[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'accepted':[{'id':x.get('mathdb_id',x.get('problem_ids')),'title':x.get('title'),'status':x.get('status')}for x in j.get('accepted',[]) if isinstance(x,dict)],'excluded':j.get('excluded',[]),'reserved_id_hits':{str(i):[(m.start(),p.read_text()[max(0,m.start()-100):m.end()+100])for m in re.finditer(r'\b'+str(i)+r'\b',p.read_text())][:10]for i in ids}}
json.dump(out,open('outputs/context-read.json','w'),indent=2)
# Prior title search, excluding this lane and all machine outputs that can contain incidental integers.
pat='|'.join(str(i)for i in ids)
import subprocess
p=subprocess.run(['rg','-n',pat,str(B),'--glob','*.md','--glob','results.json','--glob','!expanded-corpus-r99/**'],capture_output=True,text=True)
lines=[x for x in p.stdout.splitlines()if str(L)not in x];(L/'outputs/historical-id-matches.txt').write_text('\n'.join(lines)+'\n')
print('context files',len(out),'historical match lines',len(lines))
