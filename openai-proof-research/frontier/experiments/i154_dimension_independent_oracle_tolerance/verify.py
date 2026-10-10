"""I154 offline read-only evidence replay. No repair, reseal, ancestor execution.
--preseal validates prospective owned hashes supplied on stdin, before the one seal.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re,runpy,collections,math
from fractions import Fraction
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i154_dimension_independent_oracle_tolerance'
E='frontier/experiments/i154_dimension_independent_oracle_tolerance'
OLD='frontier/sources/i152_algorithmic_sampling_reconstruction_discovery'
REPORT='frontier/iterations/i154-dimension-independent-oracle-tolerance.md'
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def guard(event,args):
 if event=='open':
  mode,flags=args[1:3]
  if isinstance(mode,str) and any(c in mode for c in 'wax+'):raise AssertionError(('write denied',args[0]))
  if isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND):raise AssertionError(('write denied',args[0]))
 if event.startswith(('socket.','subprocess.','ctypes.')) or event in {'os.mkdir','os.remove','os.rename','os.rmdir','os.link','os.symlink','os.chmod','os.truncate','os.utime','os.system','os.exec','os.posix_spawn','os.fork','os.forkpty','os.chdir','os.fchdir','os.replace','os.unlink','os.chown','os.lchown','os.fchmod','os.fchown','os.ftruncate','os.setxattr','os.removexattr'}:raise AssertionError(('operation denied',event))
sys.addaudithook(guard)
CACHE={}
def read(p):
 if p not in CACHE:CACHE[p]=(R/p).read_bytes()
 return CACHE[p]
def sha(b):return hashlib.sha256(b).hexdigest()
def data(p):return json.loads(read(p))
def files(bases):
 out=set()
 for base in bases:
  for p in (R/base).rglob('*'):
   assert not p.is_symlink(),str(p)
   if p.is_file():out.add(str(p.relative_to(R)))
 return out
def ordinary_fields(o,k='task'):
 if isinstance(o,dict):return [z for a,v in o.items() for z in ordinary_fields(v,k+'/'+str(a))]
 if isinstance(o,list):return [z for a,v in enumerate(o) for z in ordinary_fields(v,k+'/'+str(a))]
 return ['FIELD '+k+'\n'+(o if isinstance(o,str) else json.dumps(o,ensure_ascii=False))]
def decoded_leaves(o):
 if isinstance(o,dict):return [z for v in o.values() for z in decoded_leaves(v)]
 if isinstance(o,list):return [z for v in o for z in decoded_leaves(v)]
 if not isinstance(o,str):return [json.dumps(o,ensure_ascii=False)]
 out=[];pos=start=0;decoder=json.JSONDecoder()
 while pos<len(o):
  m=re.search(r'[\[{]',o[pos:])
  if m is None:break
  k=pos+m.start()
  try:v,n=decoder.raw_decode(o[k:])
  except ValueError:pos=k+1;continue
  if isinstance(v,(dict,list)):
   out.extend(p.strip() for p in o[start:k].split('\n\n') if p.strip());out.extend(decoded_leaves(v));pos=start=k+n
  else:pos=k+1
 out.extend(p.strip() for p in o[start:].split('\n\n') if p.strip())
 return out
def marked_pieces(txt,pattern):
 ms=list(re.finditer(pattern,txt));return [(m.group(1),txt[m.end():ms[i+1].start() if i+1<len(ms) else len(txt)].strip()) for i,m in enumerate(ms)]
def check_context():
 tasks=[('152-algorithmic-sampling-reconstruction-discovery',S,'f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379',709),('148-polynomial-index-torus-subpackets',OLD,'077429f244aecba0a0aa34f05b1bae0ceeab003aa99fd32ce60c8e4830213fc4',949),('145-arithmetic-automorphic-discovery','frontier/sources/i148_polynomial_index_torus_subpackets',None,601),('142-uniform-algebraic-allocation','frontier/sources/i145_arithmetic_automorphic_discovery',None,600),('139-diffuse-weighted-positivity','frontier/sources/i142_uniform_algebraic_allocation',None,649),('136-birational-positivity-discovery','frontier/sources/i139_diffuse_weighted_positivity',None,537)]
 for name,base,h,n in tasks:
  p='frontier/iterations/iteration'+name+'-task.json'
  if h:assert sha(read(p))==h
  assert read(base+'/direct-context.txt').decode()=='\n\n'.join(ordinary_fields(data(p)))+'\n'
  assert len(read(base+'/direct-context.txt').decode().splitlines())==n
 cov=data(OLD+'/context-decoding-coverage.json');unique=data(OLD+'/context-unique.json')
 roots=sorted({re.split(r'/(?:task|\d+)(?:/|$)',x['field'],maxsplit=1)[0] for x in cov})
 allparts=[]
 for root in roots:
  pattern=r'(?m)^FIELD ([^\n]+)\n' if root.endswith('/direct-context.txt') else r'(?m)^\[(\d+)\]\n'
  for _,part in marked_pieces(read(root).decode(),pattern):allparts.extend(decoded_leaves(part))
 assert len(unique)==2232 and len(cov)==3570
 assert collections.Counter(allparts)==collections.Counter(unique[x['piece']] for x in cov)
 stream=read(OLD+'/context-unique.txt').decode();p=marked_pieces(stream,r'(?m)^\[(\d+)\]\n')
 assert [int(k) for k,v in p]==list(range(len(unique))) and [v for k,v in p]==unique
 assert len(stream.splitlines())==7800
 # Raw paragraph coverage is independently tied to exact character positions.
 paras=data(OLD+'/context-paragraphs.json');pcov=data(OLD+'/context-paragraph-coverage.json')
 for c in pcov:assert read(c['path']).decode()[c['start_char']:c['end_char']]==paras[c['piece']]
 # Validate the older recursively decoded field records against the frozen source objects.
 base='frontier/sources/i136_birational_positivity_discovery'
 oldpieces=dict(marked_pieces(read(base+'/context-reading.txt').decode(),r'(?m)^\[(\d+)\]\n'))
 oldcov=data(base+'/context-coverage.json');freeze=data(base+'/input-freeze.json')
 rootmap={x['path']:x['snapshot'] for x in freeze if any(c['field'].startswith(x['path']) for c in oldcov)}
 fields={}
 for c in oldcov:fields.setdefault(c['field'],[]).append(oldpieces[str(c['piece'])])
 decoder=json.JSONDecoder()
 for field,parts in fields.items():
  root=max((p for p in rootmap if field==p or field.startswith(p+'/')),key=len)
  raw=read(rootmap[root]).decode();obj=json.loads(raw) if root.endswith('.json') else raw
  tail=field[len(root):].lstrip('/')
  for key in tail.split('/') if tail else []:
   if key.startswith('embedded@'):obj=decoder.raw_decode(obj[int(key.split('@')[1]):])[0]
   elif isinstance(obj,list):obj=obj[int(key)]
   else:obj=obj[key]
  assert all(p in obj for p in parts) if isinstance(obj,str) else parts==[json.dumps(obj,ensure_ascii=False)]
 # Every ordinary source leaf, including all recursively embedded JSON leaves, is read.
 readset=set(unique)
 for root,snapshot in rootmap.items():
  raw=read(snapshot).decode();obj=json.loads(raw) if root.endswith('.json') else raw
  missing=set(decoded_leaves(obj))-readset
  assert not missing,('uncovered original decoded leaves',root,[x[:100] for x in list(missing)[:3]])
 parent=data(S+'/snapshots/frontier/experiments/i152-parent-verification.json');assert json.loads(parent['stdout'])==parent['result']
 return {'unique_decoded_pieces':len(unique),'decoded_field_coverage':len(cov),'paragraph_coverage':len(pcov),'older_field_coverage':len(oldcov),'mandatory_decoded_lines':709}
def main():
 pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or pre
 inv=data(S+'/inventory.json');owned=inv['owned_paths'];assert owned==sorted(set(owned));assert inv['allowed_live_ledger_drift']==LEDGERS
 sealpath=S+'/seal.json';valpath=E+'/validation.json';actual=files([S,E])|{REPORT};expected=set(owned)
 if pre:
  assert not (R/sealpath).exists()
  if valpath not in actual:expected.remove(valpath)
  hashes=json.load(sys.stdin);assert set(hashes)==set(owned)-{valpath}
 else:
  expected.add(sealpath);sealed=data(sealpath);hashes=sealed['sha256'];assert list(hashes)==owned
  assert data(valpath)['status']=='PASS' and data(valpath)['exit_code']==0
 assert actual==expected,{'extra':sorted(actual-expected),'missing':sorted(expected-actual)}
 for p,h in hashes.items():assert sha(read(p))==h,('owned bytes',p)
 inh=data(S+'/inheritance.json');assert inh['live_ledgers']==LEDGERS
 refs=inh['immutable'];assert [x['path'] for x in refs]==sorted({x['path'] for x in refs})
 for x in refs:
  assert x['path'] not in LEDGERS and not re.search(r'/(?:i|iteration)(151|153)[-_]',x['path'])
  assert sha(read(x['path']))==x['sha256'],('immutable inherited',x['path'])
 inherited_count=0
 for a in inh['anchors']:
  assert sha(read(a['seal']))==a['sha256'];oldseal=data(a['seal']);oldinv=data(a['inventory']);pp=set(oldinv['owned_paths'])
  assert set(oldseal['sha256'])==pp
  assert files([a['base'],a['base'].replace('/sources/','/experiments/')])|{p for p in pp if p.startswith('frontier/iterations/')}==pp|{oldinv['seal_path']}
  for p,h in oldseal['sha256'].items():assert sha(read(p))==h,('ancestor sealed bytes',p)
  inherited_count+=len(pp)
 drift=[]
 for x in data(S+'/input-freeze.json'):
  assert sha(read(x['snapshot']))==x['sha256']
  if x['path'] in LEDGERS:
   if sha(read(x['path']))!=x['sha256']:drift.append(x['path'])
  else:assert read(x['path'])==read(x['snapshot'])
 context=check_context()
 newpass=data(S+'/read-manifest.json')['passages']
 for x in inh['inherited_passages']+newpass:
  b=read(x['local']);assert sha(b)==x['file_sha256'];ls=b.decode().splitlines() if x['convention'].startswith('splitlines') else b.decode().split('\n')
  assert 1<=x['start']<=x['end']<=len(ls)
  part='\n'.join(ls[x['start']-1:x['end']]);assert sha(part.encode())==x['passage_sha256']
  if 'ending' in x:assert x['ending']==ls[x['end']-1]
  if 'line_count' in x:assert x['line_count']==len(ls)
  if 'passage' in x:assert x['passage']==part
 for path,n in [(S+'/direct-context.txt',709),(OLD+'/context-unique.txt',7800)]:
  covered={i for x in newpass if x['local']==path for i in range(x['start'],x['end']+1)};assert covered==set(range(1,n+1))
 assert sha(read(S+'/original-audit-report.md'))=='694f98b401ef41fd778c16a201496b6d105c1143ca48129d1c17875bd3647fa5'
 assert data(S+'/reading-notes.json')['original_audit_completed_before_discovery'] is True
 # Exactly one flat corpus traversal within this replay; no recursive ancestor replay.
 domain=data('frontier/sources/i112_inverse_boundary_discovery/search-domain.json')
 tree=data('frontier/sources/i112_inverse_boundary_discovery/snapshots/sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
 assert len(tree)==13223 and sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
 assert len(domain)==len(blobs)==10373 and {x['path'] for x in domain}==set(blobs)
 lexical=[data(p) for p in inh['lexical_records']]+[data(S+'/lexical-search.json')];patterns={}
 for lex in lexical:
  for k,expr in lex['patterns'].items():assert k not in patterns;patterns[k]=re.compile(expr)
 computed={k:[] for k in patterns};pdfs=0
 for x in domain:
  b=read(x['local']);o=b if x['local']==x['original_local'] else read(x['original_local'])
  assert sha(b)==x['sha256'] and sha(o)==x['original_sha256']
  assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha']
  pdfs+=x['kind']=='outside_pdf'
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for k,rx in patterns.items():
    mm=list(rx.finditer(line))
    if mm:computed[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
 assert pdfs==776
 for lex in lexical:
  for k,v in lex['results'].items():assert computed[k]==v,('lexical multiset and positions',k)
 bypath={x['path']:x for x in domain}
 for x in data(S+'/selected-source-bindings.json'):assert x==bypath[x['path']]
 flat=data(S+'/flat-traversal.json');assert flat['status']=='PASS'
 assert flat['bindings']==[dict(path=x['path'],text_sha256=x['sha256'],original_sha256=x['original_sha256'],kind=x['kind']) for x in domain]
 assert flat['lexical_counts']=={k:len(v) for k,v in computed.items()}
 overlaps={}
 for p in ['frontier/sources/i136_birational_positivity_discovery/overlap-search.json','frontier/sources/i145_arithmetic_automorphic_discovery/overlap-search.json',OLD+'/overlap-search.json',S+'/overlap-search.json']:
  ov=data(p);rx=re.compile(ov['expression']);result=[];assert ov['paths']==sorted(set(ov['paths']))
  for x in ov.get('refs',[]):assert sha(read(x['path']))==x['sha256']
  for path in ov['paths']:
   assert not re.search(r'/(?:i|iteration)(151|153)[-_]',path)
   for i,line in enumerate(read(path).decode().splitlines(),1):
    mm=list(rx.finditer(line))
    if mm:result.append(dict(path=path,splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
  assert result==ov['results'];overlaps[p]=len(result)
 for receipt in ['retrieval.json','additional-retrieval.json']:
  for x in data(S+'/primary/'+receipt):
   if 'error' in x:continue
   assert x['status']==200 and sha(read(x['path']))==x['sha256']
   if 'text_path' in x:assert sha(read(x['text_path']))==x['text_sha256']
 assert sys.dont_write_bytecode
 print('ALL immutable owned/inherited/context/corpus/lexical/primary/passage bytes: PASS; ONLY new finite diagnostics begin',file=sys.stderr,flush=True)
 diag=runpy.run_path(str(R/E/'diagnostics.py'))['run']();assert diag['status']=='PASS'
 result=dict(status='PASS',mode='preseal read-only' if pre else 'sealed read-only',owned_files=len(owned),immutable_direct_and_inherited=len(refs),inherited_sealed_artifacts=inherited_count,tree_entries=13223,manuscripts=749,original_blob_positions=10373,inherited_pdf_text_bindings=pdfs,context=context,new_read_passages=len(newpass),inherited_read_passages=len(inh['inherited_passages']),lexical_matched_lines={k:len(v) for k,v in computed.items()},lexical_occurrences={k:sum(len(x['spans']) for x in v) for k,v in computed.items()},overlap_lines=overlaps,immutable_preflight_before_diagnostics=True,ancestor_verifiers_invoked=0,ancestor_diagnostics_invoked=0,inherited_pdf_reextractions=0,allowed_live_ledger_drift=drift,new_finite_diagnostics=diag,scope='Evidence and finite checks only; no universal-proof, contribution, acceptance, priority or human/formal certification.')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
