"""Offline immutable replay followed by new finite diagnostics. No repair/reseal."""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib,re,runpy
from pathlib import Path
from collections import Counter,defaultdict

def guard(event,args):
 if event=='open':
  mode=args[1];flags=args[2]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('Read-only replay blocks writing')
 if event.startswith(('socket.','subprocess.','urllib.','http.client.','ctypes.')) or event in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime','os.exec','os.posix_spawn'}:
  raise RuntimeError('Offline replay blocks '+event)
sys.addaudithook(guard)
S=Path('frontier/sources/i138_nonlinear_dynamics_discovery');X=Path('frontier/experiments/i138_nonlinear_dynamics_discovery')
REPORT=Path('frontier/iterations/i138-nonlinear-dynamics-discovery.md')
OLD=Path('frontier/sources/i114_quantum_information_discovery')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert sys.argv[1:] in ([],['--preseal'])
preseal=sys.argv[1:]==['--preseal'];sealpath=S/'seal.json';receiptpath=S/'preseal-validation.json'
assert preseal != sealpath.exists(), 'Preseal only before the one final seal; sealed mode requires seal'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(Path(p).read_bytes())
def inactive(p):assert not re.search(r'(?:^|/)(?:i|iteration)(?:136|137)(?:[-_/])',str(p)),p
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=sha(b),bytes=len(b))
def check(r,pathkey='path',hashkey='sha256',sizekey='bytes'):
 p=r[pathkey];inactive(p);b=Path(p).read_bytes();assert sha(b)==r[hashkey],p
 if sizekey in r:assert len(b)==r[sizekey],p
 return b
def inventory(source,experiment,report,exclude=()):
 paths=[Path(report)];dirs=[]
 for base in map(Path,(source,experiment)):
  assert not base.is_symlink();dirs.append(str(base))
  for p in base.rglob('*'):
   assert not p.is_symlink(),p
   if p.is_file():paths.append(p)
   elif p.is_dir():dirs.append(str(p))
   else:raise AssertionError(str(p))
 return sorted(str(p) for p in paths if str(p) not in set(map(str,exclude))),sorted(dirs)
# Authenticate all owned files before interpreting any manifest or running code.
owned,dirs=inventory(S,X,REPORT,[sealpath]+([receiptpath] if preseal else []))
assert len(set(owned))==len(owned)
if not preseal:
 sealed=load(sealpath);assert [r['path'] for r in sealed['files']]==owned
 assert sealed['directories']==dirs
 for r in sealed['files']:check(r)
validated=[row(p) for p in owned if p!=str(receiptpath)]
if not preseal:
 receipt=load(receiptpath);assert receipt['status']=='PASS' and receipt['mode']=='preseal-read-only'
 assert receipt['validated_files']==validated
refs=load(S/'references.json');assert [r['path'] for r in refs]==sorted(set(r['path'] for r in refs))
refmap={r['path']:r for r in refs}
assert not set(refmap)&MUTABLE
for r in refs:check(r)
# Check exact original package inventories in a single flat union, never execute their verifiers.
packages=load(S/'inherited-packages.json');assert len(packages)==8
for pack in packages:
 check(pack['seal']);z=load(pack['seal']['path'])
 names,ds=inventory(pack['source'],pack['experiment'],pack['report'],[pack['seal']['path']])
 assert sorted(r['path'] for r in z['files'])==names,pack['source']
 assert sorted(z['directories'])==ds
 for r in z['files']:
  assert refmap[r['path']]['sha256']==r['sha256']
  if 'bytes' in r:assert refmap[r['path']]['bytes']==r['bytes']
assert packages[-1]['seal']['sha256']=='5b655f088507e8a8d87e4919c91b199064f70b4cf8f681d8ab315eaf2b3b7cdf'
# One original-map traversal, preserving PDF/text distinctions and exact Git blob identities.
domain=load(OLD/'search-domain.json');tree=load(OLD/'snapshots/sources/preprints-tree.json')
assert not tree['truncated'];assert len(tree['tree'])==13223
blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
assert len(blobs)==len(domain)==10373 and len(set(r['path'] for r in domain))==10373
roots={r['path'].split('/')[1] for r in domain};assert len(roots)==749
kinds=Counter();total=0;corpus=[]
for r in domain:
 inactive(r['original_local']);inactive(r['local'])
 b=Path(r['original_local']).read_bytes();total+=len(b)
 assert sha(b)==r['original_sha256'],r['path']
 git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert git==r['git_sha']==blobs[r['path']]['sha'],r['path']
 view=b if r['local']==r['original_local'] else Path(r['local']).read_bytes()
 assert sha(view)==r['sha256'],r['path']
 kinds[r['kind']]+=1
 if r['kind']=='corpus':corpus.append(r['local'])
assert dict(kinds)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257}
assert total==627365628
assert sorted(corpus)==load(OLD/'corpus-rg-inventory.json')
corpusroot=Path('frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints')
assert sorted(str(p) for p in corpusroot.rglob('*') if p.is_file())==sorted(corpus)
assert {r['path'] for r in domain}==set(blobs)
# Immutable snapshots; only four live ledger originals may drift.
drift=[];snaps=load(S/'snapshots.json')
for r in snaps:
 check(r,'snapshot')
 if r['path'] in MUTABLE:
  if sha(Path(r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
 else:check(r)
assert load(S/'snapshots/sources/upstream.json')['commit']==PIN
# Exact ranges and endings. Truncated attempts are recorded but excluded from coverage.
reads=load(S/'read-manifest.json');coverage=defaultdict(set)
for r in reads:
 b=check(r);t=json.loads(b)[r['field']] if r['field'] else b.decode('utf-8');ls=t.splitlines()
 assert len(ls)==r['total'] and 1<=r['start']<=r['end']<=len(ls)
 assert sha('\n'.join(ls[r['start']-1:r['end']]).encode())==r['range_sha256']
 assert b.count(b'\n')==r['raw_lf'] and b.endswith(b'\n')==r['terminal_lf']
 assert ls[r['end']-1]==r['ending']
 assert r['display_status'] in {'supplied','truncated-attempt'}
 if r['display_status']=='supplied':coverage[r['path']].update(range(r['start'],r['end']+1))
chunks=load(S/'context-chunks.json');groups=defaultdict(list)
for r in chunks:
 b=check(r);ls=b.decode().splitlines();t='\n'.join(ls[r['line_start']-1:r['line_end']])
 assert t[r['char_start']:r['char_end']]==r['text']
 assert sha(r['text'].encode())==r['chunk_sha256'] and r['ending']==r['text'][-120:]
 assert r['display_status'] in {'supplied','supplied-after-recovery'}
 groups[(r['path'],r['line_start'],r['line_end'])].append(r)
for (p,a,b),rs in groups.items():
 rs.sort(key=lambda r:r['char_start']);pos=0
 for r in rs:assert r['char_start']==pos;pos=r['char_end']
 assert pos==len('\n'.join(Path(p).read_text().splitlines()[a-1:b]))
 coverage[p].update(range(a,b+1))
mandatory={120:'d1b09ad8939c4842ddba3c672336e31f52ea6b0ec0433ac6e0ace2cbacad292d',123:'c0a4216b88cf7bde8e7ff4517c0d4fb2144e5457d1ab57fc5315f1d739653172',126:'38e2d007ce9cb236a9601392a586e72263279bdc28744e394d8997cd457f6651',129:'96547471b969b143cc84a80c6efdc12897315973c2ab322c4ae5ee18cbdd9147',132:'72aa941eb08f8b305ce8a3f9eb35ce8ebda5bcf929f49a84f34211d3cb91c4e7',135:'13354761b44abcbda2e755f0c6de23951e28598861582ee05b6277659720dba2'}
for n,digest in mandatory.items():
 matches=[r for r in snaps if Path(r['snapshot']).name.startswith('iteration'+str(n)+'-') and r['snapshot'].endswith('-task.json')]
 assert len(matches)==1
 raw=Path(matches[0]['snapshot']);assert sha(raw.read_bytes())==digest;z=load(raw)
 stem=raw.stem
 bp=S/'decoded'/f'{stem}-brief.txt';op=S/'decoded'/f'{stem}-other.json'
 assert bp.read_text()==z['brief']+'\n';assert load(op)=={k:v for k,v in z.items() if k!='brief'}
 for p in (bp,op):
  missing=set(range(1,len(p.read_text().splitlines())+1))-coverage[str(p)]
  assert not missing,(str(p),sorted(missing))
binding=load(S/'direct-context-binding.json')
for k in ('task','report','parent'):check(binding[k])
task=load(binding['task']['path']);brief=task['brief']
assert binding['all_other_fields']=={k:v for k,v in task.items() if k!='brief'}
assert brief.split('--- FULL I135 REPORT ---\n',1)[1].split('\n--- FINALIZED I135 PARENT RESPONSE ---',1)[0].strip()==Path(binding['report']['path']).read_text().strip()
parent=json.loads(brief.split('--- FINALIZED I135 PARENT RESPONSE ---\n',1)[1]);assert parent==load(binding['parent']['path'])
assert parent['exit_code']==0 and parent['result']['status']=='PASS'
assert parent['seal_sha256']==packages[-1]['seal']['sha256']
for r in load(S/'ledger-excerpts.json'):
 b=check(r);t=b.decode()[r['start_character']:r['end_character']]
 assert t==r['text'] and sha(t.encode())==r['range_sha256']
# Selected source inventory and exact lexical multisets, without claims of semantic novelty.
family=load(S/'family-roots.json');assert family==sorted(set(family)) and len(family)==6
selected=load(S/'selected-inventory.json')
assert selected==[r for r in domain if r['path'].split('/')[1] in family] and len(selected)==81
bymap={r['local']:r for r in domain}
for r in load(S/'source-bindings.json'):
 d=bymap[r['local']];assert r['path']==d['path'] and r['sha256']==d['sha256']
 assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['path']
lex={}
for label in ('source','overlap'):
 q=load(S/(label+'-query.json'));assert q['files']==sorted(set(q['files'])) and q['flags']=='IGNORECASE'
 result=[];rx=re.compile(q['pattern'],re.I)
 for p in q['files']:
  inactive(p);assert p in refmap
  for line,text in enumerate(Path(p).read_text(errors='replace').splitlines(),1):
   for m in rx.finditer(text):result.append(dict(path=p,line=line,start=m.start(),end=m.end(),text=m.group(),line_text=text))
 assert result==load(S/(label+'-results.json')),label
 lex[label]=len(result)
# Byte-bound HTTP products; only HTML views are deterministically reconstructed offline.
rep=load(S/'representations.json');check(rep['html_converter'])
convert=runpy.run_path(rep['html_converter']['path'])['convert'];htmls=pdfs=failed=0
for r in load(S/'http-log.json'):
 if r.get('status')!=200:
  assert 'error' in r;failed+=1;continue
 b=check(r);check(r,'text_path','text_sha256','text_bytes')
 if r['path'].endswith('.html'):
  assert convert(b.decode('utf-8',errors='replace'))==Path(r['text_path']).read_text();htmls+=1
 else:
  assert b.startswith(b'%PDF-') and r['extraction_exit']==0;pdfs+=1
assert (htmls,pdfs,failed)==(3,3,1)
# This boundary is intentional: every immutable byte/binding above precedes diagnostics.
new=runpy.run_path(str(X/'check.py'))['run']();assert new['status']=='PASS'
print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,original_positions=len(domain),original_bytes=total,domain_kinds=dict(kinds),corpus_traversals=1,tree_entries=len(tree['tree']),manuscript_roots=len(roots),flat_reference_count=len(refs),inherited_packages=len(packages),inherited_diagnostics_mode='Frozen finalized I135 parent receipt only; no inherited verifier or diagnostic executed',inherited_diagnostic_receipt_sha256=binding['parent']['sha256'],read_records=len(reads),complete_recursive_contexts=len(mandatory),context_character_chunks=len(chunks),lexical_occurrences=lex,html_views=htmls,new_pdf_text_bindings=pdfs,new_diagnostics=new,owned_files_without_seal=len(owned),owned_directories=len(dirs),permitted_mutable_drift=sorted(drift),validated_files=validated,scope='Immutable evidence and finite exact identities only; no universal proof, contribution or priority certification'),indent=2))
