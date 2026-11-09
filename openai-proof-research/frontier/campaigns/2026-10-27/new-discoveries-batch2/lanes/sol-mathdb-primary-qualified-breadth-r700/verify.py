"""Independent read-only verifier. Run via verify.sh. No upstream code execution."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r699';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p): return json.loads(p.read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size mismatch',str(p)); assert sha(b)==e['sha256'],('hash mismatch',str(p))
def exact(root,m,negative=None):
 entries=m['files']; assert len({e['path'] for e in entries})==len(entries)
 if negative=='hash':entries[0]['sha256']='0'*64
 if negative=='size':entries[0]['size']+=1
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}; expected={e['path'] for e in entries}|set(m['excluded_exact_paths'])
 # Named receipts may not yet exist during manifest creation.
 actual|=set(m['excluded_exact_paths'])
 if negative=='extra-file':actual.add('unexpected-negative-payload')
 assert actual==expected,('exact payload mismatch',sorted(actual^expected))
 for e in entries:
  p=root/e['path'];assert not p.is_symlink();check(p,e)
def run():
 negative=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 exact(D,load(D/'manifest.json'),negative)
 for e in load(D/'flat-bindings.json'):check(Path(e['path']),e)
 exact(I,load(I/'manifest.json'))
 for e in load(I/'bindings.json'):
  for k in ['original','copy']:check(Path(e[k]),e)
 cm=load(C/'manifest.json'); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]; assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 coverage=load(I/'coverage-delta.json'); assert len(coverage)==8383
 active=load(I/'active-breadth-reservations.json');assert len(active)==3
 prot=set()
 for s in active:prot.update(s['protected_ids']);prot.update(s['active_hypothesis_ids'])
 seen=set(); names=set()
 for s in active:
  ids=set(s['ids']);assert len(ids)==len(s['ids'])==50; assert not ids&set(map(int,coverage)) and not ids&seen and not ids&prot;seen|=ids;names.add(s['lane'])
 assert names=={'claude-mathdb-primary-qualified-breadth-r628','sol-mathdb-primary-qualified-breadth-r698','sol-mathdb-primary-qualified-breadth-r700'}
 own=load(I/'reserved-ids-r700.json');q=load(I/'queue-r700.json');target=set(own['ids']);assert own['coverage_baseline']==8383 and target=={e['mathdb_id'] for e in q}
 assert sum(1 for _ in (I/'routing-queue.jsonl').open())==10000
 rows=load(D/'literal-records.json');disp=load(D/'dispositions.json');assert len(rows)==len(disp)==50
 assert {e['record']['mathdb_id'] for e in rows}=={e['mathdb_id'] for e in disp}==target
 dd={e['mathdb_id']:e for e in disp};rr={e['record']['mathdb_id']:e for e in rows};found=set()
 # Scan originals without displaying or reviewing adjacent scientific records.
 for e in chunks:
  p=C/e['path']
  with p.open() as f:
   for line_no,line in enumerate(f,1):
    obj=json.loads(line);i=obj.get('mathdb_id')
    if i not in target:continue
    assert i not in found;found.add(i);x=rr[i];d=dd[i]
    canonical=sha(json.dumps(obj,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
    assert obj==x['record'];assert str(p)==x['chunk']==d['corpus_chunk'] and line_no==x['line']==d['corpus_line']
    assert canonical==x['canonical_record_sha256']==d['canonical_record_sha256']
    assert obj['statement']==d['exact_utf8_statement'];assert sha(obj['statement'].encode())==d['statement_utf8_sha256']
    assert d['classification'] in {'complete','incomplete','definition-dependent','scope-ambiguous'} and d['classification_reason'] and d['quantifiers'] and d['technical_assessment']
    assert d['accepted_credit']==0 and not d['prior_cleared']
 assert found==target
 proposals=load(D/'proposals.json');assert isinstance(proposals,list) and len(proposals)<=3
 for e in load(D/'source-provenance.json'):
  for k in ['pdf','text']:
   if k in e:check(Path(e[k]['path']),e[k])
 for s in load(D/'selected-passages.json'):
  lo,hi=s['lines'];lines=Path(s['text_file']).read_text().splitlines();assert '\n'.join(lines[lo-1:hi])==s['text']
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'baseline':8383,'chunks':20,'frozen_inputs':8,'reservation_sets':3,'proposals':len(proposals),'mathematics_novelty_acceptance':'NOT CERTIFIED'}))
if __name__=='__main__':
 try:run()
 except Exception as e:print('VERIFY FAIL:',repr(e),file=sys.stderr);sys.exit(1)
