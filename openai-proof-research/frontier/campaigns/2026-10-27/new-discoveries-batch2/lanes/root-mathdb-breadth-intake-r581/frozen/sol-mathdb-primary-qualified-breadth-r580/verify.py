#!/usr/bin/env python3
"""Independent read-only verifier. Run only through the fixed helper_guard.py."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def J(p):return json.loads(p.read_text())
def H(b):return hashlib.sha256(b).hexdigest()
def check(p,r):
 b=p.read_bytes();assert len(b)==r.get('size',r.get('bytes')),(str(p),'size');assert H(b)==r['sha256'],(str(p),'hash')
def payload(d,m):
 actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-EX
 assert actual=={r['path'] for r in m['files']},'exact payload/extra-file mismatch'
 for r in m['files']:check(d/r['path'],r)
def main():
 payload(D,J(D/'manifest.json'))
 bindings=J(D/'flat-bindings.json')
 for r in bindings:check(Path(r['path']),r)
 L=D.parent;I=L/'root-mathdb-breadth-intake-r579';C=L/'pi-mathdb-full-corpus-inventory-r301'
 m=J(I/'manifest.json'); actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert actual=={r['path'] for r in m['files']}
 for r in m['files']:check(I/r['path'],r)
 for r in J(I/'bindings.json'):
  check(Path(r['original']),r);check(Path(r['copy']),r)
 m=J(C/'manifest.json');chunks=[r for r in m['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
 for r in chunks+m['frozen_inputs']:check(C/r['path'],r)
 reserve=J(I/'reserved-ids.json');ids=set(reserve['ids']);assert len(ids)==50 and reserve['lane']==D.name
 covered=set(map(int,J(I/'coverage-delta.json')));assert len(covered)==5433
 seen=set()
 for r in J(I/'active-breadth-reservations.json'):
  s=set(r['ids']);assert len(s)==50 and not s&(seen|covered|set(reserve['protected_ids']));seen|=s
 assert ids<=seen and not ids&set(reserve['other_active_reservations'])
 assert {r['mathdb_id'] for r in J(I/'queue.json')}==ids
 stored={r['id']:r for r in J(D/'literal-records.json')};dis={r['mathdb_id']:r for r in J(D/'dispositions.json')};assert len(stored)==len(dis)==50 and set(stored)==set(dis)==ids
 found=set()
 for c in chunks:
  p=C/c['path']
  for n,line in enumerate(p.open(),1):
   a=json.loads(line);i=a['mathdb_id']
   if i not in ids:continue
   found.add(i);r=stored[i];x=dis[i];s=a['statement'];h=H(json.dumps(a,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
   assert a==r['record'] and h==r['canonical_record_sha256']==x['canonical_record_sha256']
   assert x['statement']==s and x['statement_utf8_sha256']==H(s.encode())
   assert r['chunk']==x['chunk']==str(p) and r['line']==x['line']==n
   assert x['scope_flags']['literal_statement_read'] and x['accepted_credit']==0
 assert found==ids and len(J(D/'proposals.json'))<=3
 for r in J(D/'source-provenance.json'):
  if 'sha256' in r:check(D/r['path'],r)
 for r in J(D/'derivative-bindings.json'):check(D/r['path'],r)
 return dict(integrity='PASS',rows=50,baseline_record_reviews=5433,chunks=20,frozen_inputs=8,flat_files=len(bindings),math_or_novelty_pass=False)
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
