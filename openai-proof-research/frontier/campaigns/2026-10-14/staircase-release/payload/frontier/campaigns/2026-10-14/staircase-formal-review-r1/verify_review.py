#!/usr/bin/env python3
"""Read-only frozen review verification, optionally comparing live inputs. MIT, Myeongjin Kang 2026."""
import argparse, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
 if not ok: raise ValueError(message)
def matches(p,row):
 return p.is_file() and not p.is_symlink() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
def main():
 parser=argparse.ArgumentParser(); parser.add_argument('--live-inputs',action='store_true'); args=parser.parse_args()
 manifest=json.loads((HERE/'output-manifest.json').read_text()); expected={r['path']:r for r in manifest['files']}
 actual={p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p != HERE/'output-manifest.json'}
 require(actual==set(expected),'Review output inventory mismatch')
 for name,row in expected.items(): require(matches(HERE/name,row),'Review bytes/hash mismatch: '+name)
 inputs=json.loads((HERE/'input-manifest.json').read_text())['files']
 authorprefix='frontier/campaigns/2026-10-14/staircase-formal-v1/'
 authorrows=[r for r in inputs if r['path'].startswith(authorprefix)]
 require(len(authorrows)==18,'Incomplete original author inventory')
 for row in authorrows: require(matches(HERE/'author-copy'/row['path'][len(authorprefix):],row),'Frozen author copy differs: '+row['path'])
 author=json.loads((HERE/'author-copy/output-manifest.json').read_text())
 require(len(author['files'])==17,'Unexpected original output manifest')
 for row in author['files']: require(matches(HERE/'author-copy'/row['path'],row),'Copied author manifest mismatch: '+row['path'])
 manuscript=next(r for r in inputs if r['path'].endswith('staircase-manuscript/main.tex'))
 require(matches(HERE/'context/main.tex',manuscript),'Frozen manuscript snapshot differs')
 receipt=json.loads((HERE/'audit-receipt.json').read_text())
 require(receipt['status']=='PASS','No complete independent audit receipt')
 require(receipt['fresh_source_sha256']==sha(HERE/'author-copy/StaircaseSupport.lean'),'Source receipt mismatch')
 require(receipt['review_source_sha256']==sha(HERE/'ReviewSupport.lean'),'Reviewer source receipt mismatch')
 require(receipt['fresh_olean_sha256']==json.loads((HERE/'author-copy/validation.json').read_text())['fresh_support_olean_sha256'],'Different fresh olean receipt')
 labels=['fresh-source','author-types','author-controls','review-controls','review-types','mutation-missing-inverse','mutation-right-coordinate-shift','mutation-zero-normalization']
 require([r['label'] for r in receipt['runs']]==labels,'Incomplete audit stages')
 for run,count in zip(receipt['runs'],[0,20,6,0,26,0,0,0]):
  p=HERE/'logs'/(run['label']+'.log'); log=p.read_text()
  require(sha(p)==run['log_sha256'] and run['passed'],'Stale or failed run: '+run['label'])
  if run['expected']=='success':
   require(run['exit_code']==0 and not any(t in log for t in ['error:','warning:','sorryAx']),'Unsuccessful positive stage')
   rows=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
   reports=len(rows)+len(re.findall('does not depend on any axioms',log))
   require(reports==count==run['axiom_reports'],'Axiom report count mismatch')
   for row in rows:
    axioms=set(re.sub(r'\.\{[^}]*\}','',row).split(', '))-{''}
    require(axioms<=ALLOWED,'Unexpected axiom')
  else:
   require(run['exit_code']!=0 and 'error:' in log and 'unsolved goals' in log and 'sorryAx' not in log,'Not a semantic mutation rejection')
 for f in ['ReviewSupport.lean','author-copy/StaircaseSupport.lean','author-copy/Controls.lean']:
  require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',(HERE/f).read_text()),'Forbidden token in accepted source')
 for name in ['types','controls']:
  a=HERE/'logs'/('author-'+name+'.log'); b=HERE/'author-copy/logs'/('types-and-axioms.log' if name=='types' else 'controls.log')
  require(a.read_bytes()==b.read_bytes(),'Independent author logs differ')
 lock=json.loads((HERE/'author-copy/lake-manifest.json').read_text())
 require(receipt['dependency_revisions']=={p['name']:p['rev'] for p in lock['packages']},'Lock differs from checked revisions')
 require(not manifest['full_staircase_formalization'] and manifest['scoped_verdict']=='PASS','Invalid scope fields')
 if args.live_inputs:
  for row in inputs: require(matches(ROOT/row['path'],row),'Live input differs from review snapshot: '+row['path'])
 print('PASS: frozen review inventory/hashes, copied author package, manuscript snapshot, fresh-source/type/axiom receipts, and semantic mutation rejections'+('; all live input hashes also match' if args.live_inputs else ' (live input freshness not required)'))
if __name__=='__main__': main()
