"""Offline, read-only flat replay; all immutable checks precede new diagnostics."""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib,re,runpy,bisect
from pathlib import Path
from collections import Counter,defaultdict

def guard(event,args):
 if event=='open':
  mode,flags=args[1:3]
  if isinstance(mode,str) and any(c in mode for c in 'wax+') or isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND):raise RuntimeError('read-only replay blocks writes')
 if event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.')) or event in {'os.system','os.fork','os.forkpty','os.unlink','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime','os.exec','os.posix_spawn'}:raise RuntimeError('offline replay blocks '+event)
sys.addaudithook(guard)
S=Path('frontier/sources/i153_many_body_spectral_discovery');X=Path('frontier/experiments/i153_many_body_spectral_discovery');REPORT=Path('frontier/iterations/i153-many-body-spectral-discovery.md')
OLD=Path('frontier/sources/i114_quantum_information_discovery');PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert sys.argv[1:] in ([],['--preseal'])
preseal=sys.argv[1:]==['--preseal'];sealpath=S/'seal.json';receiptpath=S/'preseal-validation.json'
assert preseal != sealpath.exists(),'preseal only before single seal; sealed default mode only'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(Path(p).read_bytes())
def allowed(p):
 p=Path(p);assert not re.search(r'(?:^|/)(?:i|iteration)(?:151|152)(?:[-_/])',str(p)),p
 assert not p.is_absolute() and '..' not in p.parts and not p.is_symlink(),p
 assert p.resolve().is_relative_to(Path.cwd().resolve()),p
hashcache={}
def hashes(p):
 p=str(p);allowed(p)
 if p not in hashcache:
  b=Path(p).read_bytes();hashcache[p]=(sha(b),len(b),hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())
 return hashcache[p]
def row(p):
 h,n,_=hashes(p);return dict(path=str(p),sha256=h,bytes=n)
def check(r,key='path',h='sha256',size='bytes'):
 z=hashes(r[key]);assert z[0]==r[h],r[key]
 if size in r:assert z[1]==r[size],r[key]
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
 z=load(receiptpath);assert z['status']=='PASS' and z['mode']=='preseal-read-only' and z['validated_files']==validated
refs=load(S/'references.json');assert [r['path'] for r in refs]==sorted(set(r['path'] for r in refs));refmap={r['path']:r for r in refs}
assert not set(refmap)&MUTABLE
for r in refs:check(r)
packs=load(S/'inherited-packages.json');assert len(packs)==13
for pack in packs:
 check(pack['seal']);z=load(pack['seal']['path']);files,ds=inventory(pack['source'],pack['experiment'],pack['report'],[pack['seal']['path']])
 assert sorted(r['path'] for r in z['files'])==files and sorted(z['directories'])==ds
 for r in z['files']:
  assert refmap[r['path']]['sha256']==r['sha256'],r['path']
  if 'bytes' in r:assert refmap[r['path']]['bytes']==r['bytes']
assert packs[-1]['seal']['sha256']=='bbb6cc9d6f95b94cc4ea80cf79df9d11aac7105b4ba9af0dc525679f3df66695'
# ONE flat traversal, with cached digest triples avoiding duplicate original byte hashing.
domain=load(OLD/'search-domain.json');tree=load(OLD/'snapshots/sources/preprints-tree.json')
assert not tree['truncated'] and len(tree['tree'])==13223
blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
assert len(domain)==len(blobs)==10373 and {r['path'] for r in domain}==set(blobs)
roots={r['path'].split('/')[1] for r in domain};assert len(roots)==749
kinds=Counter();total=0;corpus=[];domainmap={}
for r in domain:
 h,n,g=hashes(r['original_local']);total+=n
 assert h==r['original_sha256'] and g==r['git_sha']==blobs[r['path']]['sha'],r['path']
 assert hashes(r['local'])[0]==r['sha256'],r['path'];kinds[r['kind']]+=1;domainmap[r['path']]=r
 if r['kind']=='corpus':corpus.append(r['local'])
assert dict(kinds)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257} and total==627365628
assert sorted(corpus)==load(OLD/'corpus-rg-inventory.json')
assert sorted(str(p) for p in Path('frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints').rglob('*') if p.is_file())==sorted(corpus)
for r in load(S/'manybody-bindings.json'):assert r==domainmap[r['path']]
drift=[]
for r in load(S/'snapshots.json'):
 check(r,'snapshot')
 if r['path'] in MUTABLE:
  if sha(Path(r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
 else:check(r)
assert load(S/'snapshots/sources/upstream.json')['commit']==PIN
for r in load(S/'conversation-reading.json'):check(r)
coverage=defaultdict(list);reads=load(S/'read-manifest.json')
for r in reads:
 check(r);t=Path(r['path']).read_bytes().decode('utf-8');a,b=r['char_start'],r['char_end'];part=t[a:b]
 assert 0<=a<=b<=len(t)==r['total_characters']
 assert sha(part.encode())==r['range_sha256'] and part[-160:]==r['ending']
 assert t.count('\n')==r['raw_lf'] and len(t.splitlines())==r['splitlines'] and t.endswith('\n')==r['terminal_lf']
 assert t[:a].count('\n')+1==r['start_line'] and t[:b].count('\n')+1==r['end_line']
 starts=[];pos=0
 for line in t.splitlines(keepends=True):starts.append(pos);pos+=len(line)
 assert r['splitlines_start']==bisect.bisect_right(starts,a) and r['splitlines_end']==bisect.bisect_right(starts,max(a,b-1))
 if r['display_status']=='supplied':coverage[r['path']].append((a,b))
 else:assert r['display_status'].startswith('truncated')
cv=[]
for p,intervals in sorted(coverage.items()):
 merged=[]
 for a,b in sorted(intervals):
  if merged and a<=merged[-1][1]:merged[-1][1]=max(b,merged[-1][1])
  else:merged.append([a,b])
 n=len(Path(p).read_text());cv.append(dict(path=p,supplied_ranges=merged,characters=n,full_supplied=merged==[[0,n]],semantic_scope='Supplied displays; hash coverage alone is not reading'))
assert cv==load(S/'coverage.json')
contexts=load(S/'contexts.json');assert len(contexts)==11
for c in contexts:
 assert hashes(c['raw'])[0]==c['sha256']==hashes(c['snapshot'])[0]
 assert Path(c['raw']).read_bytes()==Path(c['snapshot']).read_bytes()
assert contexts[-1]['sha256']=='2d906d6f02a3e834b36afb34d3ceb4bf3b2468f29e1b3c53fc83e24b8fc53b9e'
codec=runpy.run_path(str(X/'context_codec.py'))['decode'];values=codec(contexts,load)
for name,value in zip(['decoded-lines.json','decoded-fields.json','decoded-view.txt','scalar-occurrences.json','scalar-values.txt'],values):
 assert (load(S/name) if name.endswith('.json') else (S/name).read_text())==value,name
assert len(values[0])==3478
full={r['path'] for r in cv if r['full_supplied']}
for p in [S/'decoded-view.txt',S/'scalar-values.txt',S/'external/bdf-long.txt','frontier/sources/i147_computational_lower_bound_discovery/external/crossings.txt','frontier/sources/i147_computational_lower_bound_discovery/external/ggj-v2.txt','frontier/sources/i150_near_critical_crossing_circuit_bounds/external/kintali.txt']:
 assert str(p) in full,p
for needle in ['A-Fock-space-inequality-and-the-Laughlin','Uniform-Stability-of-the-Spherical','Positive-eigenvalues-of-the-relative-SU-2','The-unique-threshold-bound-state-of-the-SU-N']:
 assert any(needle in p and p.endswith('.pdf.txt') for p in full),needle
for p in {r['path'] for r in reads if r['path'].endswith('.tex')}:assert p in full,p
parentpath=S/'snapshots/frontier/experiments/i150-parent-verification.json';parent=load(parentpath)
assert json.loads(parent['stdout'])==parent['result'] and parent['result']['status']=='PASS' and parent['exit_code']==0
assert parent['seal_sha256']==packs[-1]['seal']['sha256']
assert parent['parent_review']['accepted_count']==8 and parent['parent_review']['remaining_count']==2
# Exact lexical occurrence lists, not set-only comparisons.
q=load(S/'source-query.json');assert q['files']==sorted(set(q['files']));rx=re.compile(q['pattern'],re.I);out=[]
for p in q['files']:
 assert p in refmap or p in owned;t=Path(p).read_text();offset=0
 for no,line in enumerate(t.splitlines(keepends=True),1):
  clean=line.splitlines()[0] if line.splitlines() else ''
  for m in rx.finditer(clean):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=offset+m.start(),absolute_end=offset+m.end(),text=m.group(),line_text=clean))
  offset+=len(line)
assert out==load(S/'source-results.json');lex={'source':len(out)}
for suffix in ['', '-2']:
 q=load(S/('overlap-query'+suffix+'.json'));out=[]
 for p in q.get('paths',q.get('files',[])):
  assert p in refmap;t=Path(p).read_text()
  if suffix:
   for term in q['terms']:
    for m in re.finditer(re.escape(term),t,re.I):out.append(dict(path=p,term=term,match=m.group(),position=m.start(),line=t[:m.start()].count('\n')+1,context=t.splitlines()[t[:m.start()].count('\n')]))
  else:
   offset=0
   for no,line in enumerate(t.splitlines(keepends=True),1):
    for term in q['terms']:
     for m in re.finditer(re.escape(term),line,re.I):out.append(dict(path=p,sha256=hashes(p)[0],term=term,line=no,start=offset+m.start(),end=offset+m.end(),match=m.group(),text=line.rstrip('\n')))
    offset+=len(line)
 expected=load(S/('overlap-results'+suffix+'.json'))
 # Preserve exact ordered records once ordered by their recorded iteration convention.
 key=lambda r:(r['path'],r.get('start',r.get('position')),r['term'])
 assert sorted(out,key=key)==sorted(expected,key=key),('overlap',suffix)
 lex['overlap'+suffix]=len(out)
bindings=load(S/'new-bindings.json');assert len(bindings)==4
for b,r in zip(bindings,load(S/'http-log.json')):
 assert b['log']==r;check(b['source_binding']);check(b['text_binding'])
 raw=Path(r['path']).read_bytes();assert raw.startswith(b'%PDF') and sha(raw)==r['sha256'] and len(raw)==r['bytes']
 assert b['extraction_command']==['pdftotext','-layout',r['path'],b['text_binding']['path']]
 Path(b['text_binding']['path']).read_bytes().decode('utf-8')
assert hashes(S/'external/kintali-current.pdf')[0]==hashes('frontier/sources/i150_near_critical_crossing_circuit_bounds/external/kintali.pdf')[0]
for r in load(S/'current-versions.json'):
 t=Path(r['path']).read_text()[r['start']:r['end']];assert t==r['text'] and sha(t.encode())==r['sha256']
# No ancestor script executes. New finite diagnostics start only after all immutable checks.
new=runpy.run_path(str(X/'check.py'))['run']();assert new['status']=='PASS'
print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,original_positions=len(domain),original_bytes=total,domain_kinds=dict(kinds),corpus_traversals=1,tree_entries=len(tree['tree']),manuscript_roots=len(roots),flat_reference_count=len(refs),inherited_packages=len(packs),inherited_diagnostics_mode='Frozen finalized I150 and ancestor receipts only; none executed',inherited_diagnostic_receipt_sha256=hashes(parentpath)[0],complete_recursive_contexts=len(contexts),decoded_unique_lines=len(values[0]),decoded_field_occurrences=len(values[1]),scalar_occurrences=sum(map(len,values[3].values())),read_records=len(reads),full_supplied_files=len(full),lexical_occurrences=lex,new_pdf_text_bindings=len(bindings),new_diagnostics=new,owned_files_without_seal=len(owned),owned_directories=len(dirs),permitted_mutable_drift=sorted(drift),validated_files=validated,scope='Immutable evidence and finite checks only; no universal proof, complete Bose novelty audit, contribution or certification'),indent=2))
