import pathlib,json,hashlib,itertools,sys,time,subprocess
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def moves(s):
 result=set()
 for i in range(len(s)):
  for j in range(i+1,(len(s)+i)//2+1):
   k=j-i
   if s[i:j]==s[j:j+k]:result.add(s[:j]+s[j+k:])
 return result
def scientific():
 d=json.loads((L/'known81-dag.json').read_text());edges=d['edges'];m={w:int(v,16) for w,v in d['terminal_masks'].items()};ts=d['terminals'];root=d['word']
 assert len(edges)==2928 and len(ts)==81
 reachable={root};todo=[root]
 while todo:
  w=todo.pop();actual=moves(w);assert actual==set(edges[w])
  for v in actual:
   if v not in reachable:reachable.add(v);todo.append(v)
 assert reachable==set(edges)
 for w in sorted(edges,key=len):
  mask=0
  for v in edges[w]:mask|=m[v]
  if not edges[w]:mask=1<<ts.index(w)
  assert mask==m[w]
 assert m[root]==(1<<81)-1 and all(v.bit_count()!=80 for v in m.values())
 ch=edges[root];plans=json.loads((L/'union80-branch-plans.json').read_text());count=0
 for b in range(1<<len(ch)):
  u=0
  for i,c in enumerate(ch):
   if b>>i&1:u|=m[c]
  count+=u.bit_count()==80
 assert count==len(plans['all_plans'])==56
 codes=json.loads((L/'code-reflection.json').read_text())['map'];q=18
 assert all(len(c)==q for c in codes.values())
 for a,b,c in itertools.product(codes.values(),repeat=3):assert all((a+b)[r:r+q]!=c for r in range(1,q))
 for r in range(1,q):assert len({c[:r] for c in codes.values()})==3 or len({c[r:] for c in codes.values()})==3
 for n in range(1,6):
  for t in itertools.product('abc',repeat=n):
   w=''.join(t);enc=lambda w:''.join(codes[c] for c in w)
   assert moves(enc(w))=={enc(c) for c in moves(w)}
 out={'reachable':2928,'terminals':81,'all_node_counts_checked':True,'branch_subsets':2048,'size80_subsets':count,'universal_reflection_finite_conditions_independently_checked':True,'local_input_words':363}
 (L/'independent-check.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if sys.argv[1]=='science':scientific()
elif sys.argv[1]=='manifest':
 rows=[{'path':str(p.relative_to(L)),'sha256':sha(p),'size':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']]
 (L/'final-manifest.json').write_text(json.dumps(rows,indent=2)+'\n');print('manifest',len(rows))
elif sys.argv[1]=='final':
 rows=json.loads((L/'final-manifest.json').read_text())
 for r in rows:assert sha(L/r['path'])==r['sha256']
 for n in ['immutable-bindings.json','history-bindings.json','immutable-pdf-bindings.json']:
  for r in json.loads((L/n).read_text()):assert sha(pathlib.Path(r['path']))==r['sha256']
 for r in json.loads((L/'pdf-bindings.json').read_text()):assert sha(pathlib.Path(r['original']))==sha(pathlib.Path(r['copy']))==r['sha256']
 for r in json.loads((L/'derived-text-bindings.json').read_text()):
  p=pathlib.Path(r['path']);assert sha(p)==r['sha256']
  regenerated=subprocess.check_output(['pdftotext','-layout',str(p.with_suffix('.pdf')),'-']);assert hashlib.sha256(regenerated).hexdigest()==r['sha256']
 for n in ['followup','followup2','breadth']:
  for r in json.loads((L/(n+'-freeze.json')).read_text()):assert sha(pathlib.Path(r['path']))==r['sha256']
 receipt={'verified':True,'manifest_entries':len(rows),'scientific_original_copy_hashes':True,'immutable_references':True,'administrative_originals_not_asserted_unchanged':True,'exclusions':['final-manifest.json','final-verification.json'],'time':time.time(),'acceptance_or_novelty_certification':False}
 (L/'final-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
