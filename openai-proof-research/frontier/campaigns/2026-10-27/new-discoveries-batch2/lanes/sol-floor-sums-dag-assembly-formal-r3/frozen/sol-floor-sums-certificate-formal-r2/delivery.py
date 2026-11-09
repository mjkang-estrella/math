import pathlib,json,hashlib,tarfile,gzip,io,shutil,re,sys
L=pathlib.Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
def verify_inputs():
 rows=json.loads((L/'freeze.json').read_text())
 for r in rows:
  assert r['sha256']==sha(L/r['copy']),r['copy']
  if not r['copy'].startswith('administrative/'):
   assert sha(pathlib.Path(r['original']))==r['sha256'],r['original']
 pins=json.loads((L/'pins.json').read_text()); assert sha(pathlib.Path(pins['lean']))==pins['lean_sha256']
 for r in pins['packages']:
  g=pathlib.Path(pins['formal'])/'.lake/packages'/r['name']/'.git'
  h=(g/'HEAD').read_text().strip()
  if h.startswith('ref: '):h=(g/h[5:]).read_text().strip()
  assert h==r['revision'],r
 for n in ['Reduction','Symmetry','Source','Expansion']:
  assert sha(L/(n+'.lean'))==sha(L/'frozen/lanes/sol-floor-sums-source-formal-r1'/(n+'.lean'))
 for n,h in [('all-m-query.smt2','2864e469f3990f82b453b10649f93d9a177cafd2b9eb5869ae207ad5e3ebc704'),('z3-proof.sexpr','b102b526f33fe1cf0e1de3fd640ece58e8f4876a840215fae60a7edc5d2ce225')]:
  assert sha(L/'frozen/lanes/sol-floor-sums-certificate-r2/frozen'/n)==h
 return len(rows)
def setup_audit():
 mods=[]
 for p in sorted(L.glob('th_lemma_*.guard.json')):
  r=json.loads(p.read_text())
  if r['exit_code']==0:
   n=p.name.split('.')[0]; assert (L/'generated'/(n+'.olean')).is_file(); mods.append('generated.'+n)
 names=['Reduction','Symmetry','Source','Expansion']+mods
 text=(L/'frozen/lanes/sol-floor-sums-source-formal-r1/Audit.lean').read_text()
 text=text.replace('set_option format.width 160','set_option format.width 1000000')
 a=text.index('    | some i => if ');b=text.index('.contains',a)
 text=text[:a]+'    | some i => if '+json.dumps(names+['Audit'])+text[b:]
 text='\n'.join('import '+n for n in mods)+'\n'+text
 (L/'Audit.lean').write_text(text)
 (L/'replay-modules.json').write_text(json.dumps(names,indent=2)+'\n')
 (L/'replay-generated.txt').write_text(''.join(n.removeprefix('generated.')+'\n' for n in mods))
 print('audit modules',len(names))
def audit():
 decls=[];safety={};reports={};pending=None;parts=[]
 with (L/'Audit.log').open() as f:
  for line in f:
   assert 'error:' not in line and '⋯' not in line
   if m:=re.match(r'^DECL\|(.+?)\|ORIGIN\|(.+?)\|UNSAFE\|(false|true)$',line):decls.append(m.groups())
   if m:=re.match(r'^SAFETY\|(.+?)\|(.+)$',line):safety[m[1]]=m[2]
   if m:=re.match(r"^'([^']+)' depends on axioms: \[(.*)",line):pending=m[1];parts=[m[2].strip()]
   elif pending is not None:parts.append(line.strip())
   if pending is not None and ']' in ''.join(parts):
    reports[pending]=' '.join(parts).split(']')[0];pending=None;parts=[]
   if m:=re.match(r"^'([^']+)' does not depend on any axioms",line):reports[m[1]]=''
 actual={n for n,_,_ in decls}
 assert set(reports)==set(safety)==actual,dict(counts=[len(reports),len(safety),len(actual)],missing=list(actual-set(reports))[:12],extra=list(set(reports)-actual)[:12])
 ax={n:[a.strip() for a in re.sub(r'\.\{[^}]+\}','',s).split(',')] if s else [] for n,s in reports.items()}
 assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values())
 assert all(u=='false' for _,_,u in decls)
 partial=[n for n in safety if safety[n].endswith('.partial')];assert not partial
 for mod in json.loads((L/'replay-modules.json').read_text()):
  p=L/(mod.replace('.','/')+'.lean')
  assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|partial)\b',p.read_text())
 rows=[dict(name=n,origin=o,unsafe=False,safety=safety[n],axioms=ax[n]) for n,o,_ in decls]
 result={'literal_endpoint':'NOT_PROVED','actual_declaration_count':len(rows),'declarations':rows,'generated_partial_declarations':partial,'types':'Audit.log; pp.all=true; every actual declaration of all successfully built mathematical modules, no namespace filter'}
 (L/'audit-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print('actual declarations',len(rows))
def package():
 verify_inputs();audit()
 excluded={'source-only.tar.gz','archive-receipt.json','final-manifest.json','final-verification-receipt.json'}
 files=[p for p in L.rglob('*') if p.is_file() and p.suffix not in ['.olean','.ilean','.c','.o'] and str(p.relative_to(L)) not in excluded and 'fresh-replay' not in p.relative_to(L).parts]
 with (L/'source-only.tar.gz').open('wb') as f:
  with gzip.GzipFile(filename='',fileobj=f,mode='wb',mtime=0) as g:
   with tarfile.open(fileobj=g,mode='w') as t:
    for p in sorted(files):
     r=p.relative_to(L);info=tarfile.TarInfo(str(r));info.size=p.stat().st_size;info.mtime=0;info.mode=0o644;info.uid=info.gid=0
     with p.open('rb') as source:t.addfile(info,source)
 d=L/'fresh-replay';d.mkdir(exist_ok=True)
 with tarfile.open(L/'source-only.tar.gz') as t:t.extractall(d,filter='data')
 (L/'archive-receipt.json').write_text(json.dumps({'sha256':sha(L/'source-only.tar.gz'),'files':len(files),'compiled_own_artifacts':False,'status':'PARTIAL; no unconditional endpoint'},indent=2)+'\n')
 print('archive files',len(files))
def manifest():
 excluded={'final-manifest.json','final-verification-receipt.json'}
 rows={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
 (L/'final-manifest.json').write_text(json.dumps(rows,indent=2)+'\n');print('manifest',len(rows))
if __name__=='__main__':
 {'inputs':lambda:print('verified originals/copies',verify_inputs()),'setup':setup_audit,'audit':audit,'package':package,'manifest':manifest}[sys.argv[1]]()
