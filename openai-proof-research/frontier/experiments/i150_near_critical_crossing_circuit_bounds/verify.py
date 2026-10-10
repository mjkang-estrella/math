"""Offline read-only flat replay. Immutable checks precede all new finite diagnostics."""
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
 if event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.')) or event in {'os.system','os.fork','os.forkpty','os.unlink','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime','os.exec','os.posix_spawn'}:
  raise RuntimeError('offline replay blocks '+event)
sys.addaudithook(guard)
S=Path('frontier/sources/i150_near_critical_crossing_circuit_bounds');X=Path('frontier/experiments/i150_near_critical_crossing_circuit_bounds');REPORT=Path('frontier/iterations/i150-near-critical-crossing-circuit-bounds.md')
OLD=Path('frontier/sources/i114_quantum_information_discovery');PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert sys.argv[1:] in ([],['--preseal'])
preseal=sys.argv[1:]==['--preseal'];sealpath=S/'seal.json';receiptpath=S/'preseal-validation.json'
assert preseal != sealpath.exists(),'preseal only before one seal; default mode requires seal'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(Path(p).read_bytes())
def allowed(p):
 assert not re.search(r'(?:^|/)(?:i|iteration)(?:148|149)(?:[-_/])',str(p)),p
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
packs=load(S/'inherited-packages.json');assert len(packs)==12
for pack in packs:
 check(pack['seal']);z=load(pack['seal']['path']);files,ds=inventory(pack['source'],pack['experiment'],pack['report'],[pack['seal']['path']])
 assert sorted(r['path'] for r in z['files'])==files and sorted(z['directories'])==ds
 for r in z['files']:
  assert refmap[r['path']]['sha256']==r['sha256']
  if 'bytes' in r:assert refmap[r['path']]['bytes']==r['bytes']
assert packs[-1]['seal']['sha256']=='6e4ccaf5a33eedec5920f1d4493def0c4c2bd718c1decadaed94b9466c5da234'
# ONE traversal of the original map, including all original PDFs and retained text bindings.
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
contexts=load(S/'contexts.json');assert len(contexts)==10
for c in contexts:
 allowed(c['raw']);allowed(c['snapshot']);raw=Path(c['raw']).read_bytes()
 assert sha(raw)==c['sha256'] and Path(c['snapshot']).read_bytes()==raw
assert contexts[-1]['sha256']=='08b300fa389044d2e5004a5df163329827cf993a227ddd9a37b679db4c37ae68'
# Derived lossless field checks; this is owned pure code, never an ancestor verifier.
codec=runpy.run_path(str(X/'context_codec.py'))['decode'];values=codec(contexts,load)
for name,value in zip(['decoded-lines.json','decoded-fields.json','decoded-view.txt','scalar-occurrences.json','scalar-values.txt'],values):
 assert (load(S/name) if name.endswith('.json') else (S/name).read_text())==value,name
assert len(values[0])==3143 and len(values[1])==4560
def complete(p):
 p=str(p);pos=0
 for a,b in sorted(coverage[p]):assert a<=pos,(p,pos,a);pos=max(pos,b)
 assert pos==len(Path(p).read_text()),(p,pos)
for p in [S/'decoded-view.txt',S/'scalar-values.txt',S/'snapshots/frontier/iterations/i147-computational-lower-bound-discovery.md',S/'snapshots/frontier/experiments/i147-parent-verification.json','frontier/sources/i147_computational_lower_bound_discovery/external/crossings.txt','frontier/sources/i147_computational_lower_bound_discovery/external/ggj-v2.txt',S/'external/kintali.txt']:complete(p)
for p in {r['path'] for r in reads if r['path'].endswith('.tex')}:complete(p)
assert len({r['path'] for r in reads if r['path'].endswith('.tex') and any(x in r['path'] for x in ('Product-projection-localization','Regular-trajectories-pruning'))})==14
ancestor=Path('frontier/sources/i147_computational_lower_bound_discovery');task=load(contexts[-1]['snapshot']);brief=task['brief']
assert brief.split('--- FULL I144 REPORT ---',1)[1].split('--- FINALIZED I144 PARENT RESPONSE ---',1)[0].strip()==(ancestor/'snapshots/frontier/iterations/i144-critical-siphon-window-repulsion.md').read_text().strip()
assert json.loads(brief.split('--- FINALIZED I144 PARENT RESPONSE ---',1)[1])==load(ancestor/'snapshots/frontier/experiments/i144-parent-verification.json')
pp=S/'snapshots/frontier/experiments/i147-parent-verification.json';parent=load(pp)
assert json.loads(parent['stdout'])==parent['result'] and parent['result']['status']=='PASS'
assert parent['seal_sha256']==packs[-1]['seal']['sha256'] and parent['exit_code']==0
assert parent['parent_review']['accepted_count']==8 and parent['parent_review']['remaining_count']==2
lex={}
for label in ['source','overlap']:
 q=load(S/(label+'-query.json'));assert q['files']==sorted(set(q['files']))
 rx=re.compile(q['pattern'],re.I);out=[]
 for p in q['files']:
  allowed(p);assert p in refmap or p in owned
  t=Path(p).read_bytes().decode('utf-8');offset=0
  for no,line in enumerate(t.splitlines(keepends=True),1):
   clean=line.splitlines()[0] if line.splitlines() else ''
   for m in rx.finditer(clean):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=offset+m.start(),absolute_end=offset+m.end(),text=m.group(),line_text=clean))
   offset+=len(line)
 assert out==load(S/(label+'-results.json'));lex[label]=len(out)
bindings=load(S/'new-bindings.json');logs=load(S/'http-log.json');assert len(bindings)==len(logs)==4
for b,r in zip(bindings,logs):
 assert all(b[k]==v for k,v in r.items()),r['path']
 raw=check(b['source_binding']);txt=check(b['text_binding']);txt.decode('utf-8')
 assert b['status']==200 and raw.startswith(b'%PDF') and sha(raw)==b['sha256'] and len(raw)==b['bytes']
 assert b['extraction_exit']==0 and b['extraction_command']==['pdftotext','-layout',b['path'],b['text']]
for r in load(S/'current-versions.json'):
 t=Path(r['path']).read_text()[r['start']:r['end']];assert t==r['text'] and sha(t.encode())==r['sha256']
# All immutable evidence checks precede these NEW finite calculations. No ancestor code executes.
new=runpy.run_path(str(X/'check.py'))['run']();assert new['status']=='PASS'
print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,original_positions=len(domain),original_bytes=total,domain_kinds=dict(kinds),corpus_traversals=1,tree_entries=len(tree['tree']),manuscript_roots=len(roots),flat_reference_count=len(refs),inherited_packages=len(packs),inherited_diagnostics_mode='Frozen finalized I147 receipt and all ancestor receipts only; none executed',inherited_diagnostic_receipt_sha256=sha(pp.read_bytes()),complete_recursive_contexts=len(contexts),decoded_unique_lines=len(values[0]),decoded_field_occurrences=len(values[1]),scalar_occurrences=sum(map(len,values[3].values())),read_records=len(reads),lexical_occurrences=lex,new_pdf_text_bindings=len(bindings),new_diagnostics=new,owned_files_without_seal=len(owned),owned_directories=len(dirs),permitted_mutable_drift=sorted(drift),validated_files=validated,scope='Immutable evidence and finite exact checks only; not universal mathematics, contribution or certification'),indent=2))
