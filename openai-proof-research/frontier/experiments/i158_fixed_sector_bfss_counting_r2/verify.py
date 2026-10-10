"""I158 offline read-only byte replay; no ancestor code executes. No repair mode."""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib,re,importlib.util,math,itertools
from pathlib import Path
from collections import Counter,defaultdict
from fractions import Fraction

def guard(event,args):
 if event=='open':
  mode,flags=args[1:3]
  if isinstance(mode,str) and any(c in mode for c in 'wax+'):raise RuntimeError('read-only: open mode')
  if isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND):raise RuntimeError('read-only: open flags')
 if event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.','os.exec','os.spawn','os.posix_spawn')) or event in {'os.system','os.fork','os.forkpty','os.unlink','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime','os.putenv','os.unsetenv'}:raise RuntimeError('offline read-only: '+event)
sys.addaudithook(guard)
S=Path('frontier/sources/i158_fixed_sector_bfss_counting_r2');X=Path('frontier/experiments/i158_fixed_sector_bfss_counting_r2')
A=Path('frontier/sources/i155_fixed_sector_bfss_counting');OLD=Path('frontier/sources/i114_quantum_information_discovery')
REPORT=Path('frontier/reviews/i158-fixed-sector-bfss-counting-r2.md')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert sys.argv[1:] in ([],['--preseal'])
pre=sys.argv[1:]==['--preseal'];seal=S/'seal.json';receipt=S/'preseal-validation.json'
assert pre != seal.exists(),'Only prevalidation before first seal or sealed replay is allowed.'
def load(p):return json.loads(Path(p).read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
def allowed(p):
 p=Path(p);assert not p.is_absolute() and '..' not in p.parts and not p.is_symlink(),p
 assert p.resolve().is_relative_to(Path.cwd().resolve()),p
 assert not re.search(r'(?:^|/)(?:i|iteration)(?:156|157)(?:[-_/])',str(p)),p
cache={}
def digest(p):
 p=str(p);allowed(p)
 if p not in cache:
  b=Path(p).read_bytes();cache[p]=(sha(b),len(b),hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())
 return cache[p]
def row(p):
 h,n,_=digest(p);return dict(path=str(p),sha256=h,bytes=n)
def check(r,key='path'):
 h,n,_=digest(r[key]);assert h==r['sha256'],r[key]
 if 'bytes' in r:assert n==r['bytes'],r[key]
def inventory(s,x,r,exclude=()):
 files=[str(r)];dirs=[]
 for root in (Path(s),Path(x)):
  allowed(root);dirs.append(str(root))
  for p in root.rglob('*'):
   allowed(p)
   if p.is_dir():dirs.append(str(p))
   elif p.is_file():files.append(str(p))
   else:raise AssertionError(str(p))
 return sorted(p for p in files if p not in set(map(str,exclude))),sorted(dirs)
owned,dirs=inventory(S,X,REPORT,[seal]+([receipt] if pre else []))
assert len(owned)==len(set(owned))
if not pre:
 z=load(seal);assert [r['path'] for r in z['files']]==owned and z['directories']==dirs
 for r in z['files']:check(r)
validated=[row(p) for p in owned if p!=str(receipt)]
if not pre:
 z=load(receipt);assert z['status']=='PASS' and z['mode']=='preseal-read-only'
 assert z['validated_files']==validated and z['owned_directories']==dirs
refs=load(S/'references.json');assert [r['path'] for r in refs]==sorted(set(r['path'] for r in refs))
refmap={r['path']:r for r in refs};assert not set(refmap)&MUTABLE
for r in refs:check(r)
packs=load(S/'inherited-packages.json');assert len(packs)==15
for pack in packs:
 check(pack['seal']);z=load(pack['seal']['path'])
 fs,ds=inventory(pack['source'],pack['experiment'],pack['report'],[pack['seal']['path']])
 assert sorted(r['path'] for r in z['files'])==fs and sorted(z['directories'])==ds,pack['source']
 for r in z['files']:
  assert refmap[r['path']]['sha256']==r['sha256'],r['path']
  if 'bytes' in r:assert refmap[r['path']]['bytes']==r['bytes'],r['path']
# One flat original-map traversal per invocation. A path already hashed via refs is cached.
domain=load(OLD/'search-domain.json');tree=load(OLD/'snapshots/sources/preprints-tree.json')
assert not tree['truncated'] and len(tree['tree'])==13223
blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
assert len(domain)==len(blobs)==10373 and {r['path'] for r in domain}==set(blobs)
assert len({r['path'].split('/')[1] for r in domain})==749
kinds=Counter();total=0;pdfs=0;corpus=[]
for r in domain:
 h,n,g=digest(r['original_local']);total+=n
 assert h==r['original_sha256'] and g==r['git_sha']==blobs[r['path']]['sha'],r['path']
 assert digest(r['local'])[0]==r['sha256'],r['local']
 kinds[r['kind']]+=1
 if r['kind']=='outside_pdf':pdfs+=1
 if r['kind']=='corpus':corpus.append(r['local'])
assert dict(kinds)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257}
assert pdfs==776 and total==627365628
assert sorted(corpus)==load(OLD/'corpus-rg-inventory.json')
assert sorted(str(p) for p in Path('frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints').rglob('*') if p.is_file())==sorted(corpus)
drift=[]
for r in load(S/'snapshots.json'):
 check(r,'snapshot')
 if r['path'] in MUTABLE:
  if sha(Path(r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
 else:check(r)
assert load('sources/upstream.json')['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
contexts=load(S/'contexts.json');assert len(contexts)==13
for c in contexts:assert digest(c['raw'])[0]==c['sha256']==digest(c['snapshot'])[0]
assert contexts[-1]['sha256']=='e32170f6d05bfcfea861e801830655650dfe8fb3813b893243bf3428dda775e1'
assert digest('frontier/iterations/i155-fixed-sector-bfss-counting.md')[0]=='c6e05a0853e3232f86c8a8049cb9ecb373c9358ca58bfc1cb42c6e81d4b15f44'
for r in load(S/'conversation-reading.json'):check(r)
for r in load(A/'new-bindings.json'):check(r['pdf']);check(r['text'])
# All immutable bytes are checked before evidence reconstruction or new finite diagnostics.
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
codec=module('i158_codec',X/'codec.py')
base=load(A/'decoded-lines.json');pairs=[(c['snapshot'],load(c['snapshot'])) for c in contexts]
lines,fields=codec.decode(pairs,base)
assert fields==load(S/'decoded-fields.json') and lines[len(base):]==load(S/'decoded-new-lines.json')
assert codec.embedded(pairs)==load(S/'embedded-json-occurrences.json')
assert ''.join(f'{i}: {s}'+('' if s.endswith('\n') else '\n') for i,s in enumerate(lines[len(base):],len(base)))==(S/'decoded-new-view.txt').read_text()
sc={}
for f in fields:
 if f['kind']=='scalar':sc.setdefault(json.dumps([f['path'][-1],f['value']],ensure_ascii=False),[]).append(f['path'])
assert sc==load(S/'scalar-occurrences.json')
assert ''.join(k+'\n' for k in sc)==(S/'scalar-view.txt').read_text()
ids=set()
for f in fields:
 if f['path'][0]==contexts[-1]['snapshot']:ids.update(i for key in ['lines','prefix'] for i in f.get(key,[]) if i<len(base))
assert ''.join(f'{i}: {base[i]}'+('' if base[i].endswith('\n') else '\n') for i in sorted(ids))==(S/'i155-reused-view.txt').read_text()
reads=load(S/'read-manifest.json');coverage=defaultdict(list)
for r in reads:
 check(r);t=Path(r['path']).read_bytes().decode();a,b=r['start'],r['end']
 assert 0<=a<=b<=len(t)==r['characters']
 assert sha(t[a:b].encode())==r['range_sha256'] and t[a:b][-160:]==r['ending']
 assert t.count('\n')==r['raw_lf'] and len(t.splitlines())==r['splitlines']
 if r['status']=='supplied-and-read':coverage[r['path']].append([a,b])
 else:assert r['status']=='truncated-display-not-full-reading'
def merge(rs):
 out=[]
 for a,b in sorted(rs):
  if out and a<=out[-1][1]:out[-1][1]=max(b,out[-1][1])
  else:out.append([a,b])
 return out
cv=[]
for p,rs in sorted(coverage.items()):
 n=len(Path(p).read_text());rs=merge(rs);cv.append(dict(path=p,ranges=rs,characters=n,full=rs==[[0,n]]))
assert cv==load(S/'coverage.json')
def lexical(q,contexts=False):
 rx=re.compile(q['pattern'],re.I);out=[]
 assert q['paths']==sorted(set(q['paths']))
 for p in q['paths']:
  assert p in refmap
  off=0
  for no,line in enumerate(Path(p).read_text().splitlines(keepends=True),1):
   for m in rx.finditer(line):
    r=dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=off+m.start(),absolute_end=off+m.end(),text=m.group())
    if contexts:r['context']=line[max(0,m.start()-100):m.end()+180]
    out.append(r)
   off+=len(line)
 return out
occ=lexical(load(S/'lexical-query.json'));assert occ==load(S/'lexical-occurrences.json')
assert lexical(load(A/'lexical-query.json'))==load(A/'lexical-occurrences.json')
assert lexical(load(A/'overlap-query.json'),True)==load(A/'overlap-occurrences.json')
pending=load(S/'pending-obligations.json');assert pending['complete_requested_review'] is False and pending['overall_verdict']=='UNRESOLVED'
assert not next(r for r in cv if r['path']==str(A/'decoded-view.txt'))['full']
new={'status':'not run before seal'} if pre else module('i158_check',X/'check.py').checks()
print(json.dumps(dict(status='PASS',mode='preseal-read-only' if pre else 'sealed-read-only',complete_requested_review=False,overall_review_verdict='UNRESOLVED',scope='Immutable byte/evidence replay and finite diagnostics only; not complete semantic review, universal proof, contribution, or acceptance.',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,tree_entries=13223,manuscript_roots=749,original_positions=10373,original_bytes=total,pdf_text_bindings=pdfs,corpus_traversals=1,domain_kinds=dict(kinds),flat_references=len(refs),inherited_packages=len(packs),ancestor_execution='none',raw_recursive_contexts=len(contexts),decoded_field_occurrences=len(fields),decoded_unique_lines=len(lines),embedded_json_occurrences=len(load(S/'embedded-json-occurrences.json')),read_records=len(reads),fresh_read_files_complete=sum(r['full'] for r in cv),lexical_occurrences=len(occ),permitted_mutable_drift=sorted(MUTABLE),observed_mutable_drift=drift,owned_directories=dirs,validated_files=validated,new_diagnostics=new),indent=2))
