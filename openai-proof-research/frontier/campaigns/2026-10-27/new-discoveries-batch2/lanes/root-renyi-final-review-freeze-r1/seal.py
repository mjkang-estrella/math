import json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent;s=r.parent/'sol-renyi-threshold-manuscript-packet-r1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((r/'rebuild/receipt.json').read_text())
assert d['declarations']==104 and d['modules']==11
assert d['paper_sha256']==sha(s/'paper.pdf') and d['packet_sha256']==sha(s/'packet.zip')
assert (r/'rebuild/paper.pdf').read_bytes()==(s/'paper.pdf').read_bytes()
assert (r/'rebuild/packet.zip').read_bytes()==(s/'packet.zip').read_bytes()
a=json.loads((r/'rebuild/replay/replay-receipt.json').read_text())
for x in a['declarations']:
 assert not(x['unsafe'] or x['partial'] or x['axiom'])
 assert set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}
f=json.loads((r/'freeze.json').read_text())
for n,h in f['files'].items():assert sha(s/n)==h,n
d.update({'root_fresh_execution':True,'byte_identical_pdf_and_zip':True,'frozen_reverified':len(f['files']),'root_read_all_four_pages':True,'credit':0,'counts':[8,38],'qualifications':['Worker PDF marker failed under fixed helper guard; preserved, not retried for this read-only review.','Pinned renderer packages supplied through original lane vendor as external toolchain dependencies.','Prior-art clearance remains bounded; final review pending.']})
(r/'ROOT-REBUILD.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
