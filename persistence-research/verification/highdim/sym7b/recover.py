"""Reconcile completed search journals and atomic certificate files after interruption."""
import sys
sys.dont_write_bytecode=True
import json,pathlib,hashlib,collections
H=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from peel import load,save,ident,state,sha

def main():
 t=load(H/'tree.json');ss=t['states'];recovered=[]
 for line in (H/'search_journal.jsonl').read_text().splitlines():
  r=json.loads(line);i=r['id'];s=ss[i]
  if not any(a.get('stage')==r.get('stage') for a in s.get('attempts',[])):s.setdefault('attempts',[]).append(r)
  if r['result']=='CERTIFICATE':
   assert sha(r['file'])==r['sha256'];s.update(status='CERTIFICATE',file=r['file'],sha256=r['sha256']);s.pop('children',None)
  elif r['result']=='BUDGET' and s['status']!='CERTIFICATE':
   K,cs,p=s['K'],s['coefs'],s['p']
   # Existing OPEN decisions are preserved; recover only a recorded lost split.
   if s['status'] not in ('SPLIT','OPEN'):
    children={'empty':ident(K,cs,p+1)};ss.setdefault(children['empty'],state(K,cs,p+1))
    for c in sorted(set(cs)):
     rest=cs.copy();rest.remove(c);ch=ident(K+c*10**p,rest,p+1);children[str(c)]=ch;ss.setdefault(ch,state(K+c*10**p,rest,p+1))
    s.update(status='SPLIT',children=children);recovered.append(i)
 for f in sorted((H/'certs').glob('K*.jsonl')):
  with f.open() as stream:m=json.loads(next(stream))
  cs=[c for c,n in m['groups'] for _ in range(n)];i=ident(m['K'],cs,m['qmin'])
  if i in ss and ss[i]['status'] not in ('CERTIFICATE','SPLIT'):
   ss[i].update(status='CERTIFICATE',file=str(f),sha256=sha(f),recovered_atomic_file=True);recovered.append(i)
 # No partial generator file is admitted. Any old descendant of a recovered
 # certificate is unreachable and is pruned, while its emitted files remain replayed.
 seen=set();todo=list(t['roots'].values())
 while todo:
  i=todo.pop()
  if i in seen:continue
  seen.add(i);todo.extend(ss[i].get('children',{}).values())
 removed=sorted(set(ss)-seen);t['states']={i:s for i,s in ss.items() if i in seen}
 save(H/'tree.json',t)
 out={'result':'RECOVERED','states':len(t['states']),'recovered_states':recovered,'removed_unreachable_states':removed,'reason':'brief overlapping search-pool startup; new pool stopped and atomic outputs reconciled'}
 save(H/'recovery.json',out);print(json.dumps(out))
if __name__=='__main__':main()
