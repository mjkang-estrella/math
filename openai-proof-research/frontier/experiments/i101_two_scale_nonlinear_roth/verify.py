"""I101 FINAL OFFLINE READ-ONLY verifier. Run with python3 -B.
No network, writes, bytecode, repairs, preparation imports or resealing modes.
Integrity/finite checks do not certify analytic proofs or substantiality.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
S=Path('frontier/sources/i101_two_scale_nonlinear_roth')
E=Path('frontier/experiments/i101_two_scale_nonlinear_roth')
I=Path('frontier/sources/i99_quantitative_arithmetic_patterns_discovery')
REPORT=Path('frontier/iterations/i101-two-scale-nonlinear-roth.md')
SEAL=S/'seal.json'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
EXPECTED_RX=[r'non.?linear.{0,16}Roth',r'two.?scale|block.condition|cut.norm',r'conditional.mixing|higher.conductor|normal.character',r'(short|local).{0,30}(window|parameter|cutoff)']
def sha(b):return hashlib.sha256(b).hexdigest()
def readj(p):return json.loads(Path(p).read_text())
def owned():
 return sorted([str(REPORT)]+[str(p) for root in [S,E] for p in root.rglob('*') if p.is_file() and p!=SEAL])
def inventory():return [{'path':p,'sha256':sha(Path(p).read_bytes()),'size':Path(p).stat().st_size} for p in owned()]
def check_semantics():
 failures=[];drifts=[];stats={}
 def need(t,s):
  if not t:failures.append(s)
 refs=readj(S/'references.json')
 for r in refs:
  p=r['path'];need(r['may_drift']==(p in MUTABLE),'drift policy: '+p)
  if 'snapshot' in r:need(sha(Path(r['snapshot']).read_bytes())==r['sha256'],'snapshot: '+r['snapshot'])
  actual=sha(Path(p).read_bytes())
  if actual!=r['sha256']:
   if r['may_drift']:drifts.append({'path':p,'snapshot_sha256':r['sha256'],'live_sha256':actual})
   else:failures.append('immutable reference: '+p)
  need(not any(x in p for x in ['i98_complex_kahler','i100_defect_tolerant','i98-complex','i100-defect']),'active unrelated dependency: '+p)
 brief=readj(S/'snapshots/frontier/iterations/iteration101-two-scale-nonlinear-roth-task.json')['brief']
 need((S/'original-full-brief.txt').read_text()==brief+'\n','full original brief exact')
 for marker in ['FULL ORIGINAL I99 BRIEF:','FULL ORIGINAL I99 REPORT:','FINALIZED PARENT RESPONSE / EVIDENCE RECORD:']:
  need(marker in brief,'full-brief section '+marker)
 original=subprocess.run(['python3','-B','frontier/experiments/i99_quantitative_arithmetic_patterns_discovery/verify.py'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 need(original.returncode==0,'original I99 sealed replay')
 jr=json.loads(original.stdout);need(jr['status']=='PASS','original status')
 need(jr['seal_sha256']=='97025f8945e8a2d916ba0202e3b4ba0ecaa873f94802dcb8812fb381169aaa01','original seal identity')
 stats['inherited']=jr.get('checks',{})
 domain=readj(I/'search-domain.json')
 outside=[r for r in domain if r['kind']!='corpus']
 need(len(outside)==1033,'outside original positions')
 pdftexts=[r for r in outside if r['original_local']!=r['local'] and r['path'].lower().endswith('.pdf')]
 need(len(pdftexts)==776,'inherited outside PDF texts')
 stats['outside_originals']=len(outside);stats['outside_pdf_texts']=len(pdftexts)
 searches=readj(S/'lexical-search.json');need([r['expression'] for r in searches]==EXPECTED_RX,'exact I101 search expressions')
 patterns=[re.compile(s,re.I) for s in EXPECTED_RX];hits=[[] for _ in patterns]
 for row in domain:
  for ln,line in enumerate(Path(row['local']).read_bytes().decode(errors='replace').splitlines(),1):
   for j,rx in enumerate(patterns):
    for m in rx.finditer(line):hits[j].append({'path':row['path'],'line_splitlines':ln,'start':m.start(),'match':m.group(),'text':line})
 for i,r in enumerate(searches):
  need(r['flags']=='IGNORECASE','search flags')
  need(r['occurrences']==hits[i],'exact I101 occurrence multiset/order '+str(i))
 stats['additional_lexical_counts']=[len(h) for h in hits]
 for r in readj(S/'passages.json'):
  b=Path(r['path']).read_bytes();t=b.decode();conv=r['line_convention']
  if conv.startswith('LF;'):
   lines=t.split('\n')
   if lines[-1]=='':lines.pop()
  elif conv.startswith('splitlines;'):lines=t.splitlines()
  else:raise AssertionError('unknown line convention')
  need(sha(b)==r['source_sha256'],'passage source '+r['key'])
  need(len(lines)==r['total_lines_in_convention'],'passage line count '+r['key'])
  need(1<=r['start']<=r['end']<=len(lines),'passage range '+r['key'])
  excerpt='\n'.join(lines[r['start']-1:r['end']])+'\n'
  need(sha(excerpt.encode())==r['excerpt_sha256'],'passage bytes '+r['key'])
  if '/corpus/preprints/' in r['path']:
   need(r['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/'+r['path'].split('/corpus/preprints/')[1],'pinned passage URL')
 passage_map={r['key']:r for r in readj(S/'passages.json')}
 for ep in readj(S/'proof-endpoints.json'):
  r=passage_map[ep['key']];t=Path(r['path']).read_text()
  lines=t.splitlines() if r['line_convention'].startswith('splitlines;') else t.split('\n')
  for end in ep.get('proof_ends',[ep.get('proof_end')]):
   need(r['start']<=end<=r['end'],'proof endpoint inside excerpt '+ep['key'])
   terminal=lines[end-1]
   need(any(token in terminal for token in ['\\end{proof}','∎','\x03','completing the proof']),'proof-end marker '+ep['key'])
 for r in readj(S/'literature/retrieval.json'):
  if 'path' in r:need(sha(Path(r['path']).read_bytes())==r['sha256'],'retrieval bytes '+r['path'])
 ns={'__name__':'i101_finite_diagnostics'}
 exec(compile((E/'diagnostics.py').read_bytes(),str(E/'diagnostics.py'),'exec'),ns)
 diagnostics=ns['run']();need(diagnostics==readj(E/'diagnostics-result.json'),'exact finite diagnostic result')
 stats['finite_diagnostics']=diagnostics['counts'];stats['passages']=len(readj(S/'passages.json'))
 audit=readj(S/'contracts.json');need(all(v=='ORIGINAL PASS WITHOUT REPAIRS' for v in audit['original_verdicts'].values()),'original audit categories')
 need(audit['pass_after_repairs']==audit['fail_at_original_scope']==[],'repairs/failures lists')
 return {'status':'FAIL' if failures else 'PASS','failures':failures,'allowed_live_ledger_drift':drifts,'checks':stats,'scope':'integrity and exact finite checks; no universal proof, novelty, formal or peer-review certification'}
def verify():
 seal=readj(SEAL);result=check_semantics()
 if seal.get('schema')!='i101-seal-v1':result['failures'].append('seal schema')
 if seal['inventory']!=inventory():result['failures'].append('exact owned inventory/byte hashes')
 if any(Path(p).is_symlink() for p in owned()):result['failures'].append('owned symbolic link')
 if any(p.is_symlink() for root in [S,E] for p in root.rglob('*')):result['failures'].append('owned directory symbolic link')
 result['status']='FAIL' if result['failures'] else 'PASS'
 result['owned_inventory_files']=len(seal['inventory']);result['seal_sha256']=sha(SEAL.read_bytes())
 return result
if __name__=='__main__':
 try:result=verify()
 except Exception as exc:result={'status':'FAIL','exception':type(exc).__name__+': '+str(exc)}
 print(json.dumps(result,indent=2,sort_keys=True))
 sys.exit(0 if result['status']=='PASS' else 1)
