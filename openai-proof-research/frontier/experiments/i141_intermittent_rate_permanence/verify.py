"""Offline read-only flat replay. All immutable checks precede new finite diagnostics."""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib,re,runpy,bisect
from pathlib import Path
from collections import Counter,defaultdict

def guard(event,args):
 if event=='open':
  mode,flags=args[1:3]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('read-only replay blocks writes')
 if event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.')) or event in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime','os.exec','os.posix_spawn'}:
  raise RuntimeError('offline replay blocks '+event)
sys.addaudithook(guard)
S=Path('frontier/sources/i141_intermittent_rate_permanence');X=Path('frontier/experiments/i141_intermittent_rate_permanence');REPORT=Path('frontier/iterations/i141-intermittent-rate-permanence.md')
OLD=Path('frontier/sources/i114_quantum_information_discovery');PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert sys.argv[1:] in ([],['--preseal'])
preseal=sys.argv[1:]==['--preseal'];sealpath=S/'seal.json';receiptpath=S/'preseal-validation.json'
assert preseal != sealpath.exists(),'preseal only before one seal; default mode requires seal'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(Path(p).read_bytes())
def allowed(p):
 assert not re.search(r'(?:^|/)(?:i|iteration)(?:139|140)(?:[-_/])',str(p)),p
 assert not Path(p).is_absolute() and '..' not in Path(p).parts,p
 assert not Path(p).is_symlink(),p
 assert Path(p).resolve().is_relative_to(Path.cwd().resolve()),p

def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=sha(b),bytes=len(b))
def check(r,key='path',h='sha256',size='bytes'):
 p=r[key];allowed(p);b=Path(p).read_bytes();assert sha(b)==r[h],p
 if size in r:assert len(b)==r[size],p
 return b

def inventory(source,experiment,report,exclude=()):
 files=[str(report)];dirs=[]
 for root in (Path(source),Path(experiment)):
  allowed(root);dirs.append(str(root))
  for p in root.rglob('*'):
   allowed(p)
   if p.is_file():files.append(str(p))
   elif p.is_dir():dirs.append(str(p))
   else:raise AssertionError(str(p))
 return sorted(p for p in files if p not in set(map(str,exclude))),sorted(dirs)
owned,dirs=inventory(S,X,REPORT,[sealpath]+([receiptpath] if preseal else []))
assert len(owned)==len(set(owned))
if not preseal:
 z=load(sealpath);assert [r['path'] for r in z['files']]==owned and z['directories']==dirs
 for r in z['files']:check(r)
validated=[row(p) for p in owned if p!=str(receiptpath)]
if not preseal:
 r=load(receiptpath);assert r['status']=='PASS' and r['mode']=='preseal-read-only';assert r['validated_files']==validated
refs=load(S/'references.json');assert [r['path'] for r in refs]==sorted(set(r['path'] for r in refs))
refmap={r['path']:r for r in refs};assert not set(refmap)&MUTABLE
for r in refs:check(r)
packs=load(S/'inherited-packages.json');assert len(packs)==9
for pack in packs:
 check(pack['seal']);z=load(pack['seal']['path']);files,ds=inventory(pack['source'],pack['experiment'],pack['report'],[pack['seal']['path']])
 assert sorted(r['path'] for r in z['files'])==files and sorted(z['directories'])==ds
 for r in z['files']:
  assert refmap[r['path']]['sha256']==r['sha256']
  if 'bytes' in r:assert refmap[r['path']]['bytes']==r['bytes']
assert packs[-1]['seal']['sha256']=='672a4645b61f2a16efea8a0e6ef9cc867b376e5aa0c91f1eb8e851d037d66ef0'
# ONE original map traversal, all PDF/text bindings and Git blob identities included.
domain=load(OLD/'search-domain.json');tree=load(OLD/'snapshots/sources/preprints-tree.json')
assert not tree['truncated'] and len(tree['tree'])==13223
blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
assert len(domain)==len(blobs)==10373 and {r['path'] for r in domain}==set(blobs)
roots={r['path'].split('/')[1] for r in domain};assert len(roots)==749
kinds=Counter();total=0;corpus=[]
for r in domain:
 allowed(r['original_local']);allowed(r['local']);b=Path(r['original_local']).read_bytes();total+=len(b)
 assert sha(b)==r['original_sha256'],r['path']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_sha']==blobs[r['path']]['sha'],r['path']
 view=b if r['local']==r['original_local'] else Path(r['local']).read_bytes()
 assert sha(view)==r['sha256'],r['path'];kinds[r['kind']]+=1
 if r['kind']=='corpus':corpus.append(r['local'])
assert dict(kinds)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257} and total==627365628
assert sorted(corpus)==load(OLD/'corpus-rg-inventory.json')
assert sorted(str(p) for p in Path('frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints').rglob('*') if p.is_file())==sorted(corpus)
drift=[]
for r in load(S/'snapshots.json'):
 check(r,'snapshot')
 if r['path'] in MUTABLE:
  if sha(Path(r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
 else:check(r)
assert load(S/'snapshots/sources/upstream.json')['commit']==PIN
# Character ranges with LF line numbers and separate splitlines totals.
coverage=defaultdict(list);reads=load(S/'read-manifest.json')
for r in reads:
 b=check(r);t=b.decode('utf-8');a,bp=r['char_start'],r['char_end'];part=t[a:bp]
 assert 0<=a<=bp<=len(t)==r['total_characters']
 assert sha(part.encode())==r['range_sha256'] and part[-160:]==r['ending']
 assert t.count('\n')==r['raw_lf'] and len(t.splitlines())==r['splitlines'] and t.endswith('\n')==r['terminal_lf']
 assert t[:a].count('\n')+1==r['start_line'] and t[:bp].count('\n')+1==r['end_line']
 starts=[];pos=0
 for line in t.splitlines(keepends=True):starts.append(pos);pos+=len(line)
 assert r['splitlines_start']==bisect.bisect_right(starts,a) and r['splitlines_end']==bisect.bisect_right(starts,max(a,bp-1))
 if r['display_status']=='supplied':coverage[r['path']].append((a,bp))
 else:assert r['display_status'].startswith('truncated-attempt')
contexts=load(S/'contexts.json');assert len(contexts)==7
for c in contexts:
 raw=Path(c['raw']).read_bytes();assert sha(raw)==c['sha256'];z=json.loads(raw)
 assert load(S/'decoded'/Path(c['raw']).name)==z
 assert Path(c['brief']).read_text()==z['brief']+'\n'
 assert load(c['other'])=={k:v for k,v in z.items() if k!='brief'}
 for p in (c['brief'],c['other']):
  pos=0
  for a,b in sorted(coverage[p]):assert a<=pos,(p,pos,a);pos=max(pos,b)
  assert pos==len(Path(p).read_text()),(p,pos)
assert contexts[-1]['sha256']=='88cc27de77bc6aa9fa94830bdf2dc8cddc662bd2d75723d5671c77c6986d326b'
binding=load(S/'direct-context-binding.json');task=load(binding['task']);brief=task['brief']
rp=S/'snapshots/frontier/iterations/i138-nonlinear-dynamics-discovery.md';pp=S/'snapshots/frontier/experiments/i138-parent-verification.json'
assert brief.split('--- FULL I138 REPORT ---',1)[1].split('--- FINALIZED I138 PARENT RESPONSE ---',1)[0].strip()==rp.read_text().strip()
assert json.loads(brief.split('--- FINALIZED I138 PARENT RESPONSE ---',1)[1])==load(pp)
assert load(pp)['seal_sha256']==packs[-1]['seal']['sha256'] and load(pp)['result']['status']=='PASS'
for r in load(S/'ledger-excerpts.json'):
 t=Path(r['path']).read_text()[r['start']:r['end']];assert t==r['text'] and sha(t.encode())==r['range_sha256']
lex={}
for label in ['source','overlap']:
 q=load(S/(label+'-query.json'));assert q['files']==sorted(set(q['files']))
 rx=re.compile(q['pattern'],re.I);out=[]
 for p in q['files']:
  allowed(p);assert p in refmap or p in owned
  for no,line in enumerate(Path(p).read_text(errors='replace').splitlines(),1):
   for m in rx.finditer(line):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),text=m.group(),line_text=line))
 assert out==load(S/(label+'-results.json'));lex[label]=len(out)
html=pdf=failed=0
for r in load(S/'http-log.json'):
 if r['status']!=200:assert 'error' in r;failed+=1;continue
 b=check(r)
 if r['path'].endswith('.pdf'):
  assert b.startswith(b'%PDF-') and r['extraction_exit']==0;check(r,'text_path','text_sha256','text_bytes');pdf+=1
 else:assert r['path'].endswith('.html');html+=1
for r in load(S/'current-versions.json'):
 t=Path(r['path']).read_text()[r['start']:r['end']];assert t==r['text'] and sha(t.encode())==r['sha256']
assert (html,pdf,failed)==(3,2,1)
search=load(S/'switch-search.json');assert len(search['rows'])==12
assert all(sorted(r['order'])==list(range(12)) for r in search['rows'])
# All immutable checks above. No ancestor verifier, diagnostic or numerical simulation is executed.
new=runpy.run_path(str(X/'check.py'))['run']();assert new['status']=='PASS'
print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,original_positions=len(domain),original_bytes=total,domain_kinds=dict(kinds),corpus_traversals=1,tree_entries=len(tree['tree']),manuscript_roots=len(roots),flat_reference_count=len(refs),inherited_packages=len(packs),inherited_diagnostics_mode='Frozen finalized I138 receipt and immutable ancestor receipts only; none executed',inherited_diagnostic_receipt_sha256=sha(pp.read_bytes()),complete_recursive_contexts=len(contexts),read_records=len(reads),lexical_occurrences=lex,new_pdf_text_bindings=pdf,raw_html_products=html,failed_retrievals=failed,new_diagnostics=new,owned_files_without_seal=len(owned),owned_directories=len(dirs),permitted_mutable_drift=sorted(drift),validated_files=validated,scope='Immutable evidence and finite exact checks only; not universal dynamics or contribution certification'),indent=2))
