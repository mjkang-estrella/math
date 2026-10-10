"""One flat immutable replay. Offline/read-only; no ancestor program execution."""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib,re,difflib,runpy
from pathlib import Path
from collections import Counter,defaultdict

def guard(event,args):
 if event=='open':
  mode,flags=args[1:3]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('read-only replay denies writes')
 if event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.')) or event in {'os.system','os.fork','os.forkpty','os.posix_spawn','os.exec','os.unlink','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime'}:
  raise RuntimeError('offline replay denies '+event)
sys.addaudithook(guard)
S=Path('frontier/sources/i155_fixed_sector_bfss_counting');X=Path('frontier/experiments/i155_fixed_sector_bfss_counting')
REPORT=Path('frontier/iterations/i155-fixed-sector-bfss-counting.md')
OLD=Path('frontier/sources/i114_quantum_information_discovery')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert sys.argv[1:] in ([],['--preseal'])
preseal=sys.argv[1:]==['--preseal'];sealpath=S/'seal.json';receipt=S/'preseal-validation.json'
assert preseal != sealpath.exists(),'Only prevalidation before a seal, or immutable sealed replay; no repair/reseal mode.'
def load(p):return json.loads(Path(p).read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
def allowed(p):
 p=Path(p)
 assert not p.is_absolute() and '..' not in p.parts and not p.is_symlink(),p
 assert not re.search(r'(?:^|/)(?:i|iteration)(?:151|154)(?:[-_/])',str(p)),p
 assert p.resolve().is_relative_to(Path.cwd().resolve()),p
cache={}
def hashes(p):
 p=str(p);allowed(p)
 if p not in cache:
  b=Path(p).read_bytes();cache[p]=(sha(b),len(b),hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())
 return cache[p]
def row(p):
 h,n,_=hashes(p);return dict(path=str(p),sha256=h,bytes=n)
def check(r,key='path'):
 h,n,_=hashes(r[key]);assert h==r['sha256'],r[key]
 if 'bytes' in r:assert n==r['bytes'],r[key]
def inventory(s,x,r,exclude=()):
 fs=[str(r)];ds=[]
 for root in (Path(s),Path(x)):
  allowed(root);ds.append(str(root))
  for p in root.rglob('*'):
   allowed(p)
   if p.is_file():fs.append(str(p))
   elif p.is_dir():ds.append(str(p))
   else:raise AssertionError(str(p))
 return sorted(p for p in fs if p not in set(map(str,exclude))),sorted(ds)
owned,dirs=inventory(S,X,REPORT,[sealpath]+([receipt] if preseal else []))
assert len(owned)==len(set(owned))
if not preseal:
 sealed=load(sealpath);assert [r['path'] for r in sealed['files']]==owned and sealed['directories']==dirs
 for r in sealed['files']:check(r)
validated=[row(p) for p in owned if p!=str(receipt)]
if not preseal:
 v=load(receipt);assert v['status']=='PASS' and v['mode']=='preseal-read-only'
 assert v['validated_files']==validated
refs=load(S/'references.json');assert [r['path'] for r in refs]==sorted(set(r['path'] for r in refs))
refmap={r['path']:r for r in refs};assert not set(refmap)&MUTABLE
for r in refs:check(r)
packs=load(S/'inherited-packages.json');assert len(packs)==14
for p in packs:
 check(p['seal']);z=load(p['seal']['path'])
 fs,ds=inventory(p['source'],p['experiment'],p['report'],[p['seal']['path']])
 assert sorted(r['path'] for r in z['files'])==fs and sorted(z['directories'])==ds
 for r in z['files']:
  assert refmap[r['path']]['sha256']==r['sha256'],r['path']
  if 'bytes' in r:assert refmap[r['path']]['bytes']==r['bytes']
assert packs[-1]['seal']['sha256']=='5a9417cbb3661c1a27d661f31995e604d53967471f77e6d33f88d717b1c3b619'
# The inherited original map is traversed exactly once, flat; cached path digests
# prevent repeated byte hashing through package aliases. No ancestor code runs.
domain=load(OLD/'search-domain.json');tree=load(OLD/'snapshots/sources/preprints-tree.json')
assert not tree['truncated'] and len(tree['tree'])==13223
blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
assert len(domain)==len(blobs)==10373 and {r['path'] for r in domain}==set(blobs)
assert len({r['path'].split('/')[1] for r in domain})==749
kinds=Counter();total=0;corpus=[]
for r in domain:
 h,n,g=hashes(r['original_local']);total+=n
 assert h==r['original_sha256'] and g==r['git_sha']==blobs[r['path']]['sha'],r['path']
 assert hashes(r['local'])[0]==r['sha256'],r['path']
 kinds[r['kind']]+=1
 if r['kind']=='corpus':corpus.append(r['local'])
assert dict(kinds)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257}
assert total==627365628
assert sorted(corpus)==load(OLD/'corpus-rg-inventory.json')
assert sorted(str(p) for p in Path('frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints').rglob('*') if p.is_file())==sorted(corpus)
drift=[]
for r in load(S/'snapshots.json'):
 check(r,'snapshot')
 if r['path'] in MUTABLE:
  if sha(Path(r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
 else:check(r)
assert load(S/'snapshots/sources/upstream.json')['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
for r in load(S/'conversation-reading.json'):check(r)
contexts=load(S/'contexts.json');assert len(contexts)==12
for c in contexts:
 assert hashes(c['raw'])[0]==c['sha256']==hashes(c['snapshot'])[0]
assert contexts[-1]['sha256']=='2793dd39ccfd77cbe06a40c61ae329a77167e39039ca2a63c2d1828adb41bf9f'
for r in load(S/'new-bindings.json'):
 check(r['pdf']);check(r['text'])
 assert Path(r['pdf']['path']).read_bytes().startswith(b'%PDF')
for r in load(S/'http-log.json'):
 if 'failure' not in r:
  p=S/'external'/(r['key']+'.pdf');assert hashes(p)[:2]==(r['sha256'],r['bytes'])
  assert hashes(p.with_suffix('.txt'))[:2]==(r['text_sha256'],r['text_bytes'])
# All immutable bytes have now been checked. The following reconstructs evidence,
# then (in sealed mode only) executes the small new finite normalization checks.
reads=load(S/'read-manifest.json');coverage=defaultdict(list)
for r in reads:
 check(r);t=Path(r['path']).read_bytes().decode();a,b=r['start'],r['end'];part=t[a:b]
 assert 0<=a<=b<=len(t)==r['characters']
 assert sha(part.encode())==r['range_sha256'] and part[-160:]==r['ending']
 assert t.count('\n')==r['raw_lf'] and len(t.splitlines())==r['splitlines']
 if r['status']=='supplied-and-read':coverage[r['path']].append([a,b])
 else:assert r['status'].startswith('truncated-display')
def merged(v):
 out=[]
 for a,b in sorted(v):
  if out and a<=out[-1][1]:out[-1][1]=max(out[-1][1],b)
  else:out.append([a,b])
 return out
cv=[]
for p,v in sorted(coverage.items()):
 n=len(Path(p).read_text());z=merged(v);cv.append(dict(path=p,ranges=z,characters=n,full=z==[[0,n]]))
assert cv==load(S/'coverage.json');cm={r['path']:r for r in cv}
decode=runpy.run_path(str(X/'context.py'))['decode']
lines,fields=decode([(c['snapshot'],load(c['snapshot'])) for c in contexts])
assert lines==load(S/'decoded-lines.json') and fields==load(S/'decoded-fields.json')
assert ''.join(f'{i}: {line}'+('' if line.endswith('\n') else '\n') for i,line in enumerate(lines))==(S/'decoded-view.txt').read_text()
sc={}
for f in fields:
 if f['kind']=='scalar':
  k=json.dumps([f['path'][-1],f['value']],ensure_ascii=False);sc.setdefault(k,[]).append(f['path'])
assert sc==load(S/'scalar-occurrences.json')
assert ''.join(k+'\n' for k in sc)==(S/'scalar-view.txt').read_text()
for p in (S/'decoded-view.txt',S/'scalar-view.txt'):assert cm[str(p)]['full']
difftext=''
for d in load(S/'thermal-diff-map.json'):
 assert hashes(d['base'])[0]==d['base_sha256'] and hashes(d['target'])[0]==d['target_sha256']
 a=Path(d['base']).read_text().splitlines(keepends=True);b=Path(d['target']).read_text().splitlines(keepends=True)
 assert [list(x) for x in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes()]==d['opcodes']
 assert cm[d['base']]['full']
 difftext+=''.join(difflib.unified_diff(a,b,fromfile=d['base'],tofile=d['target'],n=4))
assert difftext==(S/'thermal-diff-view.txt').read_text()
assert cm[str(S/'thermal-diff-view.txt')]['full']
for r in load(S/'bose-coverage.json'):
 check(r);t=Path(r['path']).read_text();assert len(t)==r['characters'] and t[-160:]==r['ending']
 assert r['covered']
 if r['method']=='complete direct supplied ranges':assert cm[r['path']]['full']
 else:assert r['path'] in {d['target'] for d in load(S/'thermal-diff-map.json')}
query=load(S/'lexical-query.json');rx=re.compile(query['pattern'],re.I);occ=[]
assert query['paths']==sorted(set(query['paths']))
for p in query['paths']:
 t=Path(p).read_text();offset=0
 for no,line in enumerate(t.splitlines(keepends=True),1):
  for m in rx.finditer(line):occ.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=offset+m.start(),absolute_end=offset+m.end(),text=m.group()))
  offset+=len(line)
assert occ==load(S/'lexical-occurrences.json')
oq=load(S/'overlap-query.json');orr=[];orx=re.compile(oq['pattern'],re.I)
assert oq['paths']==sorted(set(oq['paths']))
for p in oq['paths']:
 assert p in refmap
 off=0
 for no,line in enumerate(Path(p).read_text().splitlines(keepends=True),1):
  for m in orx.finditer(line):orr.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=off+m.start(),absolute_end=off+m.end(),text=m.group(),context=line[max(0,m.start()-100):m.end()+180]))
  off+=len(line)
assert orr==load(S/'overlap-occurrences.json')
diagnostics={'status':'not run before seal'} if preseal else runpy.run_path(str(X/'check.py'))['checks']()
print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,
 original_positions=10373,original_bytes=total,tree_entries=13223,manuscript_roots=749,corpus_traversals=1,domain_kinds=dict(kinds),
 flat_references=len(refs),inherited_packages=len(packs),ancestor_execution='none',complete_recursive_contexts=len(contexts),decoded_unique_lines=len(lines),decoded_field_occurrences=len(fields),
 read_records=len(reads),full_direct_supplied_files=sum(r['full'] for r in cv),bose_operative_files=54,lexical_occurrences=len(occ),overlap_occurrences=len(orr),new_pdf_text_bindings=len(load(S/'new-bindings.json')),
 owned_files_without_seal=len(owned),owned_directories=len(dirs),permitted_mutable_drift=sorted(MUTABLE),observed_mutable_drift=drift,new_diagnostics=diagnostics,validated_files=validated,
 scope='Immutable evidence and finite arithmetic only; no mathematical proof, exhaustive literature screen, substantiality or acceptance certification.'),indent=2))
