"""I152 offline read-only verifier. ALL immutable bytes before new diagnostics.
Flat inherited evidence, one corpus traversal; no inherited execution, network,
write, subprocess, bytecode, repair or resealing. --preseal only before sealing.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re,runpy
from html.parser import HTMLParser
R=Path(__file__).resolve().parents[3];S='frontier/sources/i152_algorithmic_sampling_reconstruction_discovery';E='frontier/experiments/i152_algorithmic_sampling_reconstruction_discovery';REPORT='frontier/iterations/i152-algorithmic-sampling-reconstruction-discovery.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def audit(event,args):
 if event=='open':
  mode,flags=args[1:3]
  assert not(isinstance(mode,str) and any(c in mode for c in 'wax+')),('write forbidden',args[0])
  assert not(isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),('write forbidden',args[0])
 if event.startswith('socket.') or event in {'subprocess.Popen','os.mkdir','os.remove','os.rename','os.rmdir','os.link','os.symlink','os.chmod','os.truncate','os.utime','os.system','os.exec','os.posix_spawn','os.fork','os.chdir','os.fchdir','os.replace','os.unlink','os.rmdir','os.chown','os.lchown','os.fchmod','os.fchown','os.ftruncate','os.setxattr','os.removexattr'}:raise AssertionError(('forbidden',event))
sys.addaudithook(audit)
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
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
  if t in ('p','div','section','h1','h2','h3','h4','li','table','tr'):self.out.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip-=1
  if t in ('p','div','section','h1','h2','h3','h4','li','tr'):self.out.append('\n')
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
def extract(b):
 p=Extract();p.feed(b.decode());ls=[' '.join(l.split()) for l in ''.join(p.out).splitlines()];return ('\n'.join(l for l in ls if l)+'\n').encode()
def context_check(freeze):
 OLD='frontier/sources/i136_birational_positivity_discovery'
 stream=read(OLD+'/context-reading.txt').decode();matches=list(re.finditer(r'(?m)^\[(\d+)\]\n',stream));pieces={}
 for i,m in enumerate(matches):pieces[int(m.group(1))]=stream[m.end():matches[i+1].start() if i+1<len(matches) else len(stream)].strip()
 assert list(pieces)==list(range(1263)) and len(stream.splitlines())==4499
 cov=data(OLD+'/context-coverage.json');roots={x['path']:x['snapshot'] for x in freeze if any(c['field'].startswith(x['path']) for c in cov)}
 fields={}
 for c in cov:fields.setdefault(c['field'],[]).append(pieces[c['piece']])
 decoder=json.JSONDecoder()
 for field,parts in fields.items():
  root=max((p for p in roots if field==p or field.startswith(p+'/')),key=len)
  raw=read(roots[root]).decode();obj=json.loads(raw) if root.endswith('.json') else raw
  tail=field[len(root):].lstrip('/')
  for key in tail.split('/') if tail else []:
   if key.startswith('embedded@'):obj=decoder.raw_decode(obj[int(key.split('@')[1]):])[0]
   elif isinstance(obj,list):obj=obj[int(key)]
   else:obj=obj[key]
  if isinstance(obj,str):
   assert all(p in obj for p in parts),('decoded field content',field)
  else:assert parts==[json.dumps(obj,ensure_ascii=False)],('decoded scalar',field,parts,obj)
 # Every decoded ordinary leaf has coverage, and all text outside decoded JSON blocks is covered.
 def walk(obj,field):
  if isinstance(obj,dict):
   for k,v in obj.items():walk(v,field+'/'+str(k))
  elif isinstance(obj,list):
   for i,v in enumerate(obj):walk(v,field+'/'+str(i))
  elif isinstance(obj,str):
   spans=[]
   prefix=field+'/embedded@'
   starts=sorted({int(x[len(prefix):].split('/')[0]) for x in fields if x.startswith(prefix)})
   for start in starts:
    val,end=decoder.raw_decode(obj[start:]);spans.append((start,start+end));walk(val,prefix+str(start))
   pos=0;outside=[]
   for lo,hi in spans:
    if lo<pos:continue
    outside.append(obj[pos:lo]);pos=hi
   outside.append(obj[pos:]);own=fields.get(field,[])
   for block in outside:
    for par in block.split('\n\n'):
     if par.strip():assert par.strip() in own,('uncovered decoded paragraph',field,par[:100])
  else:assert field in fields,('uncovered decoded scalar',field)
 for root,snap in roots.items():
  raw=read(snap).decode();walk(json.loads(raw) if root.endswith('.json') else raw,root)
 return len(pieces),len(cov)
def main():
 pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or pre
 inv=data(S+'/inventory.json');owned=inv['owned_paths'];assert owned==sorted(set(owned));assert inv['allowed_live_ledger_drift']==LEDGERS
 actual=files([S,E])|{REPORT};expected=set(owned);sealpath=S+'/seal.json';valpath=E+'/validation.json'
 if pre:
  assert not (R/sealpath).exists()
  if valpath not in actual:expected.remove(valpath)
  assert actual==expected,dict(extra=sorted(actual-expected),missing=sorted(expected-actual))
  prospective=json.load(sys.stdin);assert set(prospective)==set(owned)-{valpath}
  for p,h in prospective.items():assert sha(read(p))==h,('preseal owned',p)
 else:
  assert actual==expected|{sealpath},dict(extra=sorted(actual-expected-{sealpath}),missing=sorted(expected-actual))
  sealed=data(sealpath);assert list(sealed['sha256'])==owned
  for p,h in sealed['sha256'].items():assert sha(read(p))==h,('owned immutable',p)
  assert data(valpath)['status']=='PASS' and data(valpath)['exit_code']==0
 inh=data(S+'/inheritance.json');assert inh['live_ledgers']==LEDGERS
 refs=inh['immutable'];assert [x['path'] for x in refs]==sorted({x['path'] for x in refs})
 for x in refs:
  assert x['path'] not in LEDGERS and not re.search(r'/(?:i|iteration)(150|151)[-_]',x['path'])
  assert sha(read(x['path']))==x['sha256'],('immutable direct/inherited',x['path'])
 inherited_files=0
 for a in inh['anchors']:
  assert sha(read(a['seal']))==a['sha256'];si=data(a['seal']);ii=data(a['inventory']);pp=set(ii['owned_paths'])
  assert set(si['sha256'])==pp
  assert files([a['base'],a['base'].replace('/sources/','/experiments/')])|{p for p in pp if p.startswith('frontier/iterations/')}==pp|{ii['seal_path']}
  for p,h in si['sha256'].items():assert sha(read(p))==h,('inherited sealed bytes',p)
  inherited_files+=len(pp)
 drift=[]
 for x in data(S+'/input-freeze.json'):
  b=read(x['snapshot']);assert sha(b)==x['sha256']
  if x['path'] in LEDGERS:
   if sha(read(x['path']))!=x['sha256']:drift.append(x['path'])
  else:assert read(x['path'])==b
 def decoded(obj,key='task'):
  out=[]
  if isinstance(obj,dict):
   for k,v in obj.items():out.extend(decoded(v,key+'/'+str(k)))
  elif isinstance(obj,list):
   for i,v in enumerate(obj):out.extend(decoded(v,key+'/'+str(i)))
  else:out.append('FIELD '+key+'\n'+(obj if isinstance(obj,str) else json.dumps(obj,ensure_ascii=False)))
  return out
 tasks=[('148-polynomial-index-torus-subpackets','077429f244aecba0a0aa34f05b1bae0ceeab003aa99fd32ce60c8e4830213fc4',S,949),('145-arithmetic-automorphic-discovery','728019d743f52629c3864135085b0bfaa996f8a1b6f96e3b63ae1a926043db6b','frontier/sources/i148_polynomial_index_torus_subpackets',601),('142-uniform-algebraic-allocation','9eb4cd246404b5bdad7bb1cc9d68806d73bc3dc85acc7cf0a959c279cb86fd35','frontier/sources/i145_arithmetic_automorphic_discovery',600),('139-diffuse-weighted-positivity','4efafb184bde0e6cd5b908107e0eb29670209d4488129be0cd8b8647bda40bbc','frontier/sources/i142_uniform_algebraic_allocation',649),('136-birational-positivity-discovery','fb761d762d453a405d6ce3a740f5c6ceea3c7863c372648aeed781d82ea306cd','frontier/sources/i139_diffuse_weighted_positivity',537)]
 newpass=data(S+'/read-manifest.json')['passages']
 for name,h,base,total in tasks:
  p='frontier/iterations/iteration'+name+'-task.json';assert sha(read(p))==h
  stream=base+'/direct-context.txt';assert read(stream).decode()=='\n\n'.join(decoded(data(p)))+'\n';assert len(read(stream).decode().splitlines())==total
  seen={i for x in newpass if x['local']==stream for i in range(x['start'],x['end']+1)};assert seen==set(range(1,total+1))
 OLD='frontier/sources/i136_birational_positivity_discovery';pieces,coverage=context_check(data(OLD+'/input-freeze.json'))
 assert any(x['local']==OLD+'/context-reading.txt' and x['start']==1 and x['end']==4499 for x in newpass)
 checkpoint=data(S+'/original-audit-checkpoint.json');assert checkpoint['report_audit_sha256']==sha(read(S+'/original-audit-report.md'))
 assert data(S+'/reading-notes.json')['original_audit_completed_before_discovery'] is True
 # One flat corpus traversal checks all bindings and every inherited/new lexical multiset.
 domain=data('frontier/sources/i112_inverse_boundary_discovery/search-domain.json');assert domain==data('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json')
 tree=data('frontier/sources/i112_inverse_boundary_discovery/snapshots/sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
 manuscripts=sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree);assert len(tree)==13223 and manuscripts==749 and len(domain)==len(blobs)==10373 and {x['path'] for x in domain}==set(blobs)
 lexical=[data(p) for p in inh['lexical_records']]+[data(S+'/lexical-search.json')];patterns={}
 for lex in lexical:
  for key,expr in lex['patterns'].items():assert key not in patterns;patterns[key]=re.compile(expr)
 computed={k:[] for k in patterns};pdfs=0
 for x in domain:
  b=read(x['local']);o=b if x['local']==x['original_local'] else read(x['original_local'])
  assert sha(b)==x['sha256'] and sha(o)==x['original_sha256'],('corpus bytes',x['path'])
  assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha']
  pdfs+=x['kind']=='outside_pdf'
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for key,rx in patterns.items():
    mm=list(rx.finditer(line))
    if mm:computed[key].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
 assert pdfs==776
 for lex in lexical:
  for k,v in lex['results'].items():assert computed[k]==v,('exact lexical multiset',k)
 bypath={x['path']:x for x in domain}
 for x in data(S+'/selected-source-bindings.json'):assert x==bypath[x['path']]
 for x in data(OLD+'/selected-source-bindings.json'):
  assert x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'];assert {k:v for k,v in x.items() if k!='url'}==bypath[x['path']]
 for x in inh['inherited_passages']+newpass:
  b=read(x['local']);assert sha(b)==x['file_sha256'];ls=b.decode().splitlines() if x['convention'].startswith('splitlines') else b.decode().split('\n')
  assert 1<=x['start']<=x['end']<=len(ls);part='\n'.join(ls[x['start']-1:x['end']]);assert sha(part.encode())==x['passage_sha256']
  if 'line_count' in x:assert x['line_count']==len(ls)
  if 'passage' in x:assert x['passage']==part
  if 'ending' in x:assert x['ending']==ls[x['end']-1]
 overlap_counts={}
 for p in [OLD+'/overlap-search.json','frontier/sources/i145_arithmetic_automorphic_discovery/overlap-search.json',S+'/overlap-search.json']:
  ov=data(p);rx=re.compile(ov['expression']);result=[]
  assert ov['paths']==sorted(set(ov['paths']))
  for x in ov.get('refs',[]):assert sha(read(x['path']))==x['sha256']
  for path in ov['paths']:
   assert not re.search(r'/(?:i|iteration)(150|151)[-_]',path)
   for i,line in enumerate(read(path).decode().splitlines(),1):
    mm=list(rx.finditer(line))
    if mm:result.append(dict(path=path,splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
  assert result==ov['results'];overlap_counts[p]=len(result)
 for x in data(S+'/primary/retrieval.json'):
  if 'error' in x:continue
  assert x['status']==200 and sha(read(x['local']))==x['sha256']
  if 'text_path' in x:assert x['extraction']['exit']==0 and sha(read(x['text_path']))==x['text_sha256'] and len(read(x['text_path']).decode().splitlines())==x['text_lines']
 for name,v in [('hhp',1),('picard',2)]:
  vv=[int(x) for x in re.findall(r'<strong>\[v(\d+)\]</strong>',read(S+'/primary/'+name+'.html').decode())];assert vv and max(vv)==v,(name,vv)
 flat=data(S+'/flat-traversal.json');assert flat['status']=='PASS'
 assert flat['bindings']==[dict(path=x['path'],text_sha256=x['sha256'],original_sha256=x['original_sha256'],kind=x['kind']) for x in domain]
 assert flat['lexical_counts']=={k:len(v) for k,v in computed.items()}
 assert sys.dont_write_bytecode
 print('ALL immutable owned/inherited/corpus/context/lexical/passage bytes: PASS; ONLY new finite diagnostics begin',file=sys.stderr,flush=True)
 new=runpy.run_path(str(R/E/'diagnostics.py'))['run']();assert new['status']=='PASS'
 print(json.dumps(dict(status='PASS',mode='preseal read-only' if pre else 'sealed read-only',owned_files=len(owned),immutable_direct_and_inherited=len(refs),inherited_sealed_artifacts=inherited_files,tree_entries=len(tree),manuscripts=manuscripts,original_blob_positions=len(domain),inherited_pdf_text_bindings=pdfs,decoded_context_pieces=pieces,decoded_field_coverage_records=coverage,new_read_passages=len(newpass),inherited_read_passages=len(inh['inherited_passages']),lexical_matched_lines={k:len(v) for k,v in computed.items()},lexical_occurrences={k:sum(len(x['spans']) for x in v) for k,v in computed.items()},overlap_lines=overlap_counts,immutable_preflight_before_diagnostics=True,ancestor_verifiers_invoked=0,ancestor_diagnostics_invoked=0,inherited_pdf_reextractions=0,allowed_live_ledger_drift=drift,new_finite_diagnostics=new,scope='Evidence replay and finite instances only; no universal-proof, human/formal, contribution, priority or acceptance certification.'),indent=2))
if __name__=='__main__':main()
