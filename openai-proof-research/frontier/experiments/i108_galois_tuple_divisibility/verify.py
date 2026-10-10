"""Offline READ-ONLY I108 verifier. Require python -B; optional --preseal.
No downloads, writes, bytecode, repair or reseal. Evidence/finite checks only.
Preparation scripts are not imported or executed.
"""
import sys
if not sys.dont_write_bytecode or sys.flags.optimize:raise SystemExit('Require python -B without -O')
import os,json,hashlib,re,subprocess,runpy,io,contextlib
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i108_galois_tuple_divisibility')
E=Path('frontier/experiments/i108_galois_tuple_divisibility')
REPORT=Path('frontier/iterations/i108-galois-tuple-divisibility.md')
OLD=Path('frontier/sources/i104_modular_representation_discovery')
OLDE=Path('frontier/experiments/i104_modular_representation_discovery')
SEAL=S/'seal.json';SEALHASH=S/'seal.sha256'
def readonly(event,args):
 if event=='open':
  mode,flags=args[1:3]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
   raise RuntimeError('Read-only verifier rejected write')
 if event in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','socket.connect','socket.bind','socket.getaddrinfo','os.system','os.exec','os.posix_spawn','os.fork'}:
  raise RuntimeError('Read-only/offline verifier rejected '+event)
 if event=='subprocess.Popen':
  require(args[1]==['pdftotext','-layout',str(ROOT/S/'external/bby-v1.pdf'),'-'],'Subprocess outside selective stdout-only extraction')
sys.addaudithook(readonly)
def require(ok,message):
 if not ok:raise AssertionError(message)
def blob(p):return (ROOT/p).read_bytes()
def digest(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(blob(p))
def owned():
 out=[str(REPORT)]
 for directory in [S,E]:
  for p in (ROOT/directory).rglob('*'):
   require(not p.is_symlink(),'Owned symlink '+str(p))
   if p.is_file():out.append(str(p.relative_to(ROOT)))
 return sorted(out)
def replay(script,expected):
 buffer=io.StringIO()
 with contextlib.redirect_stdout(buffer):runpy.run_path(str(ROOT/script),run_name='__main__')
 actual=json.loads(buffer.getvalue())
 require(actual==js(expected),'Finite replay mismatch '+str(script))
 return actual
def run(preseal):
 result={'mode':'preseal' if preseal else 'final','read_only':True,'offline':True,'bytecode_disabled':True}
 current=owned()
 if preseal:require(str(SEAL) not in current and str(SEALHASH) not in current,'Preseal refuses an existing seal')
 else:
  raw=blob(SEAL);require(blob(SEALHASH).decode().strip()==digest(raw),'Seal hash mismatch');seal=json.loads(raw)
  require(current==seal['owned_inventory'],'Exact owned inventory mismatch')
  require(set(seal['files'])==set(current)-{str(SEAL),str(SEALHASH)},'Seal hash scope mismatch')
  for p,h in seal['files'].items():require(digest(blob(p))==h,'Owned hash mismatch '+p)
  require(seal['drift_allowed_live_only']==['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],'Drift scope changed')
  validation=js(S/'validation-before-seal.json');require(validation['exit_code']==0 and validation['result']['status']=='PASS','Preseal validation did not pass')
 result['owned_files']=len(current)
 refs=js(S/'immutable-references.json')
 forbidden=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
 for row in refs:
  p=row['path'];require(p not in forbidden and not re.search(r'i10[67]|iteration10[67]',p),'Disallowed active dependency '+p)
  require(digest(blob(p))==row['sha256'],'Immutable reference mismatch '+p)
 result['immutable_references']=len(refs)
 require('fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' in json.dumps(js('sources/upstream.json')),'Wrong pin')
 tree=js('sources/preprints-tree.json');require(not tree.get('truncated',False) and len(tree['tree'])==13223,'Complete tree scope')
 originals={r['path']:r for r in tree['tree'] if r['type']=='blob'};require(len(originals)==10373,'Original count')
 q=js(S/'queries.json');domain=js(q['domain']);require(Counter(r['path'] for r in domain)==Counter(originals.keys()),'Exact domain path multiset')
 require(Counter(r['kind'] for r in domain)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'Domain representations')
 require(len({r['path'].split('/')[1] for r in domain})==749,'Manuscript count')
 pats={k:re.compile(v,re.I) for k,v in q['queries'].items()};hits={k:[] for k in pats}
 for row in domain:
  b=blob(row['original_local']);require(digest(b)==row['original_sha256'],'Original sha256 '+row['path'])
  git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  require(git==row['git_sha']==originals[row['path']]['sha'] and len(b)==originals[row['path']]['size'],'Original git blob '+row['path'])
  rep=b if row['local']==row['original_local'] else blob(row['local']);require(digest(rep)==row['sha256'],'Representation '+row['path'])
  for ln,line in enumerate(rep.decode('utf-8',errors='replace').splitlines(),1):
   for name,pat in pats.items():
    for m in pat.finditer(line):hits[name].append({'path':row['path'],'line':ln,'span':list(m.span()),'match':m.group(),'text':line})
 result['original_blobs']=len(domain);result['inherited_pdf_texts_hash_checked']=776;result['searches']={}
 summary=js(S/'search-summary.json')
 for name,rows in hits.items():
  rows.sort(key=lambda r:(r['path'],r['line'],r['span']))
  require((''.join(json.dumps(r,sort_keys=True,ensure_ascii=False)+'\n' for r in rows)).encode()==blob(S/('search-'+name+'.jsonl')),'Full lexical occurrence multiset '+name)
  families=sorted({r['path'].split('/')[1] for r in rows});require(summary[name]=={'occurrences':len(rows),'families':families},'Search summary '+name)
  result['searches'][name]={'occurrences':len(rows),'families':len(families)}
 for row in js(S/'passages.json')['passages']:
  b=blob(row['local']);txt=b.decode('utf-8',errors='replace');lines=txt.splitlines();chosen=lines[row['first']-1:row['last']]
  require(digest(b)==row['sha256'],'Passage source '+row['local'])
  require(len(lines)==row['splitlines_count'] and len(txt.split('\n'))==row['lf_split_count'],'Line conventions')
  require(chosen[0]==row['first_line'] and chosen[-1]==row['last_line'] and digest(('\n'.join(chosen)+'\n').encode())==row['passage_sha256'],'Passage bytes')
 result['passages']=len(js(S/'passages.json')['passages'])
 for row in js(S/'retrievals.json'):
  b=blob(S/'external'/row['name']);require(len(b)==row['bytes'] and digest(b)==row['sha256'],'Retained primary response '+row['name'])
 scope=js(S/'extraction-scope.json');require(scope['pdfs']==[str(S/'external/bby-v1.pdf')],'Selective PDF scope')
 require(scope['pdfs']==[str(p.relative_to(ROOT)) for p in sorted((ROOT/S/'external').glob('*.pdf'))],'New PDF inventory')
 for p in scope['pdfs']:
  process=subprocess.run(['pdftotext','-layout',str(ROOT/p),'-'],capture_output=True,check=False)
  require(process.returncode==0 and process.stdout==blob(p+'.txt'),'Selective extraction '+p)
 result['external_pdfs_reextracted']=len(scope['pdfs'])
 prompt=blob(S/'original-i108-prompt.txt').decode()
 envelopes=js(S/'original-task-response.json')
 pages=[json.loads(envelopes[k]['content'][0]['text'])['items'][0] for k in ['first','continuation']]
 require(pages[0]['itemId']==pages[1]['itemId'] and len(pages[0]['text'])==50000,'Original pagination identity')
 require(''.join(p['text'] for p in pages)+'\n'==prompt,'Original prompt text including documented added terminal LF')
 report=prompt.split('--- ORIGINAL REPORT ---\n',1)[1].split('\n--- FINAL PARENT RESPONSE ---',1)[0].strip()+'\n'
 require(report.encode()==blob(S/'original-i104-report-from-prompt.md')==blob(S/'snapshots/frontier/iterations/i104-modular-representation-discovery.md'),'Original report mismatch')
 require(digest(report.encode())=='3268c0b8765ad8962b07db8cef768ba06e04aef0785e35f76d822784e7bebf54','Original report expected hash')
 brief=prompt.split('--- ORIGINAL BRIEF ---\n',1)[1].split('\n--- ORIGINAL REPORT ---',1)[0]+'\n'
 require(brief.encode()==blob(S/'original-i104-brief.txt'),'Original brief mismatch')
 parent=json.loads(prompt.split('--- FINAL PARENT RESPONSE ---\n',1)[1]);require(parent==js(S/'original-i104-parent-response.json'),'Original parent response mismatch')
 require(digest(blob(OLD/'seal.json'))==parent['seal_sha256']=='405c06fb33a2c0a6a641ac5932ab2b1252f7078f15757892ea5640f16a486d91','Original seal identity')
 oldseal=js(OLD/'seal.json')
 for p,h in oldseal['files'].items():require(digest(blob(p))==h,'Original sealed artifact '+p)
 for row in parent['parent_reading']['complete_files']:require(digest(blob(row['path']))==row['sha256'],'Original parent complete-file evidence')
 for row in parent['parent_reading']['passages']:
  b=blob(row['path']);txt=b.decode();lines=txt.splitlines() if row['line_convention'].startswith('splitlines') else txt.split('\n')
  require(digest(b)==row['source_sha256'] and digest('\n'.join(lines[row['start']-1:row['end']]).encode())==row['passage_sha256'],'Original parent passage evidence')
 old=replay(OLDE/'diagnostics.py',OLDE/'diagnostics.json');require(old['cycle_reconstructions']==683,'Original rank finite replay')
 tuples=replay(E/'tuple_search.py',E/'tuple-search.json');checks=replay(E/'checks.py',E/'checks.json')
 result['finite_diagnostics']={'original_partition_checks':683,'original_tuple_cases':len(old['twisted']),'new_group_prime_cases':len(tuples['cases']),'admissible_group_prime_power_cases':sum(len(c['a']) for c in tuples['cases']),'retained_multiset_rows':sum(r['multisets'] for c in tuples['cases'] for r in c['results']),'independent':checks}
 result['status']='PASS';result['boundary']='Evidence integrity and finite replay only; no universal proof or contribution certification.'
 return result
if __name__=='__main__':
 try:
  require(sys.argv[1:] in [[],['--preseal']],'Only optional --preseal supported')
  print(json.dumps(run(sys.argv[1:]==['--preseal']),indent=2))
 except Exception as exc:
  print(json.dumps({'status':'FAIL','type':type(exc).__name__,'message':str(exc)},indent=2));raise SystemExit(1)
