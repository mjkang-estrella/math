"""I145 offline read-only verifier. ALL immutable bytes before new diagnostics.
Flat inherited evidence, one corpus traversal; no inherited execution, network,
write, subprocess, bytecode, repair or resealing. --preseal only before sealing.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re,runpy
from html.parser import HTMLParser
R=Path(__file__).resolve().parents[3];S='frontier/sources/i145_arithmetic_automorphic_discovery';E='frontier/experiments/i145_arithmetic_automorphic_discovery';REPORT='frontier/iterations/i145-arithmetic-automorphic-discovery.md'
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
  prospective=json.load(sys.stdin)
  assert set(prospective)==set(owned)-{valpath}
  for path,digest in prospective.items():assert sha(read(path))==digest,('preseal owned bytes',path)
 
 else:
  assert actual==expected|{sealpath},dict(extra=sorted(actual-expected-{sealpath}),missing=sorted(expected-actual))
  sealed=data(sealpath);assert list(sealed['sha256'])==owned
  for p,h in sealed['sha256'].items():assert sha(read(p))==h,('I145 owned bytes',p)
  assert data(valpath)['status']=='PASS' and data(valpath)['exit_code']==0
 inherited=data(S+'/inheritance.json');assert inherited['live_ledgers']==LEDGERS
 refs=inherited['immutable'];assert [x['path'] for x in refs]==sorted({x['path'] for x in refs})
 for x in refs:
  assert x['path'] not in LEDGERS and not re.search(r'/(?:i|iteration)(143|144)[-_]',x['path'])
  assert sha(read(x['path']))==x['sha256'],('immutable inherited/direct',x['path'])
 inherited_artifacts=0
 for a in inherited['anchors']:
  assert sha(read(a['seal']))==a['sha256'];si=data(a['seal']);ii=data(a['inventory']);pp=set(ii['owned_paths'])
  assert set(si['sha256'])==pp
  bases=[a['base'],a['base'].replace('/sources/','/experiments/')]
  reports={p for p in pp if p.startswith('frontier/iterations/')}
  assert files(bases)|reports==pp|{ii['seal_path']},('inherited inventory',a['base'])
  for p,h in si['sha256'].items():assert sha(read(p))==h,('inherited owned',p)
  inherited_artifacts+=len(pp)
 freeze=data(S+'/input-freeze.json');drift=[]
 for x in freeze:
  b=read(x['snapshot']);assert sha(b)==x['sha256']
  if x['path'] in LEDGERS:
   if sha(read(x['path']))!=x['sha256']:drift.append(x['path'])
  else:assert read(x['path'])==b
 mandatory='frontier/iterations/iteration142-uniform-algebraic-allocation-task.json'
 assert sha(read(mandatory))=='9eb4cd246404b5bdad7bb1cc9d68806d73bc3dc85acc7cf0a959c279cb86fd35'
 OLD='frontier/sources/i136_birational_positivity_discovery'
 pieces,coverage=context_check(data(OLD+'/input-freeze.json'))
 def decoded(obj,key='task'):
  out=[]
  if isinstance(obj,dict):
   for k,v in obj.items():out.extend(decoded(v,key+'/'+str(k)))
  elif isinstance(obj,list):
   for i,v in enumerate(obj):out.extend(decoded(v,key+'/'+str(i)))
  else:out.append('FIELD '+key+'\n'+(obj if isinstance(obj,str) else json.dumps(obj,ensure_ascii=False)))
  return out
 expected='\n\n'.join(decoded(data(mandatory)))+'\n'
 assert read(S+'/direct-context.txt').decode()==expected
 oldmandatory='frontier/iterations/iteration136-birational-positivity-discovery-task.json'
 assert sha(read(oldmandatory))=='fb761d762d453a405d6ce3a740f5c6ceea3c7863c372648aeed781d82ea306cd'
 oldstream='frontier/sources/i139_diffuse_weighted_positivity/direct-context.txt'
 assert read(oldstream).decode()=='\n\n'.join(decoded(data(oldmandatory)))+'\n'
 i139task='frontier/iterations/iteration139-diffuse-weighted-positivity-task.json'
 assert sha(read(i139task))=='4efafb184bde0e6cd5b908107e0eb29670209d4488129be0cd8b8647bda40bbc'
 i139stream='frontier/sources/i142_uniform_algebraic_allocation/direct-context.txt'
 assert read(i139stream).decode()=='\n\n'.join(decoded(data(i139task)))+'\n'
 for path,total in [(S+'/direct-context.txt',600),(i139stream,649),(oldstream,537),(OLD+'/context-reading.txt',4499)]:
  assert len(read(path).decode().splitlines())==total
  seen=set()
  for passage in data(S+'/read-manifest.json')['passages']:
   if passage['local']==path:seen.update(range(passage['start'],passage['end']+1))
  assert seen==set(range(1,total+1)),('new actual complete context reading coverage',path)
 
 assert data(S+'/original-audit-checkpoint.json')['required_i142_sha256']==sha(read(mandatory))
 assert data(S+'/reading-notes.json')['mandatory_context_completed_before_audit'] is True
 domain=data('frontier/sources/i112_inverse_boundary_discovery/search-domain.json')
 assert domain==data('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json')
 tree=data('frontier/sources/i112_inverse_boundary_discovery/snapshots/sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
 manuscripts=sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)
 assert len(tree)==13223 and manuscripts==749 and len(blobs)==len(domain)==10373 and {x['path'] for x in domain}==set(blobs)
 lexical=[data(p) for p in inherited['lexical_records']]+[data(S+'/lexical-search.json')];patterns={}
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
  for key,v in lex['results'].items():assert computed[key]==v,('lexical exact multiset',key)
 bypath={x['path']:x for x in domain}
 for x in data(OLD+'/selected-source-bindings.json'):
  assert x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']
  assert {k:v for k,v in x.items() if k!='url'}==bypath[x['path']]
 passages=inherited['inherited_passages']+data(S+'/read-manifest.json')['passages']
 for p in passages:
  b=read(p['local']);assert sha(b)==p['file_sha256']
  ls=b.decode().splitlines() if p['convention'].startswith('splitlines') else b.decode().split('\n')
  assert 1<=p['start']<=p['end']<=len(ls)
  part='\n'.join(ls[p['start']-1:p['end']]);assert sha(part.encode())==p['passage_sha256'],('passage',p['local'],p['start'])
  if 'line_count' in p:assert p['line_count']==len(ls)
  if 'passage' in p:assert part==p['passage']
  if 'ending' in p:assert ls[p['end']-1]==p['ending']
 overlap=data(OLD+'/overlap-search.json');rx=re.compile(overlap['expression']);oh=[]
 for p in overlap['paths']:
  for i,line in enumerate(read(p).decode().splitlines(),1):
   mm=list(rx.finditer(line))
   if mm:oh.append(dict(path=p,splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
 assert oh==overlap['results']
 # New overlap is an exact frozen full-report lexical domain, not a semantic-read claim.
 overlap_new=data(S+'/overlap-search.json');rx=re.compile(overlap_new['expression']);on=[]
 assert overlap_new['paths']==sorted(set(overlap_new['paths']))
 assert [r['path'] for r in overlap_new['refs']]==overlap_new['paths']
 for r in overlap_new['refs']:
  assert not re.search(r'/(?:i|iteration)(143|144)[-_]',r['path'])
  assert sha(read(r['path']))==r['sha256']
  for i,line in enumerate(read(r['path']).decode().splitlines(),1):
   mm=list(rx.finditer(line))
   if mm:on.append(dict(path=r['path'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
 assert on==overlap_new['results']
 for x in data(S+'/selected-source-bindings.json'):assert x==bypath[x['path']]
 for rec in data(S+'/primary/retrievals.json'):
  if 'failure' in rec:continue
  assert sha(read(S+'/primary/'+rec['file']))==rec['sha256']
  if 'text' in rec:
   assert rec['extraction_exit']==0
   assert sha(read(S+'/primary/'+rec['text']))==rec['text_sha256']
 # Preserve current metadata versions; do not re-extract a PDF or contact its publisher.
 for name,v in [('aka',2),('elmv09',1),('elmv11',2),('khayutin',2),('lotz',3),('ito',2),('roe',1),('dumnicki',1),('biran',2)]:
  versions=[int(x) for x in re.findall(r'<strong>\[v(\d+)\]</strong>',read(S+'/primary/'+name+'-abs.html').decode())]
  assert versions and max(versions)==v,(name,versions)
 assert sys.dont_write_bytecode
 # This is the only executable research module loaded; all immutable checks above precede it.
 print('ALL owned/inherited/corpus/lexical/context/passage immutable preflight: PASS; new finite diagnostics begin',file=sys.stderr,flush=True)
 new=runpy.run_path(str(R/E/'diagnostics.py'))['run']();assert new['status']=='PASS'
 result=dict(status='PASS',mode='preseal read-only' if pre else 'sealed read-only',owned_files=len(owned),immutable_direct_and_inherited=len(refs),inherited_sealed_artifacts=inherited_artifacts,tree_entries=len(tree),manuscripts=manuscripts,original_blob_positions=len(domain),inherited_pdf_text_bindings=pdfs,decoded_context_pieces=pieces,decoded_field_coverage_records=coverage,read_passages=len(passages),lexical_matched_lines={k:len(v) for k,v in computed.items()},lexical_occurrences={k:sum(len(x['spans']) for x in v) for k,v in computed.items()},overlap_matched_lines=len(on),overlap_reports=len(overlap_new['paths']),inherited_overlap_matched_lines=len(oh),immutable_preflight_before_diagnostics=True,recursive_verifiers_invoked=0,inherited_diagnostic_runs='none; immutable records only',selected_pdf_reextractions=0,allowed_live_ledger_drift_observed=drift,new_finite_diagnostics=new,scope='Evidence reproduction and finite instances only; no universal proof, substantiality, human review or priority certification')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
