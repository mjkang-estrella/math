import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def row(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),sha256=sha(b),bytes=len(b))
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
failure=json.loads((L/'failures.json').read_text())
if len(failure)==1:failure.append(dict(operation='second checks.py run',error='AssertionError: proposed P4 weights (2,1,2) not proper: middle degrees both3',exit=1,guard_peak_rss=16809984,guard_wall_seconds=0.08020176505669951,response='Corrected datum to (2,1,3), exact degrees(2,3,4,3); no mathematical source conclusion depended on failed datum.'))
save('failures.json',failure)
save('primary-hashes.json',dict(utc=utc,records=[row(p) for p in sorted((L/'sources').iterdir()) if p.is_file()],access_receipts='http.jsonl',policy='PDFs retained byte-for-byte as scientific originals; .txt files are pdftotext -layout derivatives, not independent sources.'))
g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('guard-binding.json',dict(utc=utc,path=str(g),sha256=sha(g.read_bytes()),AS_bytes=512*1024*1024,sampled_group_RSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,environment={'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},caps_changed=False))
save('provenance.json',dict(utc=utc,lane=str(L),result='ZERO complete resolutions; universal gap OPEN',source='arXiv:2506.21254v1 Conjecture7.1 p28',journal='10.1016/j.tcs.2026.115773: author listings only; published body unread',companion='arXiv:2303.02611v4 actual primary body; 10.1007/s00453-021-00903-x journal body unread',history='history-receipt.json: qualified r170/r172/r173/r174 union with changed-file refresh, no new echo exclusions',primary_bytes='primary-hashes.json and http.jsonl',checks=['checks.json','tree-route.json','replay-receipt.json'],administrative_context='context-* are snapshot-only; live NEXT/ledger are mutable and excluded from external scientific freeze',limits=['bounded history/index aliases, not worldwide novelty','parked historical capped intervals and merge gaps','no new current registry head access','no universal proof','no independent review or investment approval'],credit=0,no_shared_edits=True))
ex={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
payload=[row(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ex]
save('scientific-freeze.json',dict(utc=utc,records=payload,exclusions=sorted(ex),reason='Self and mutually recursive manifest/verification receipts excluded explicitly; administrative snapshot bytes included, live administrative files never frozen.'))
save('finalmanifest.json',dict(utc=utc,records=payload+[row(L/'scientific-freeze.json')],exclusions=['finalmanifest.json','manifest-verification.json'],reason='No recursive self/verification-receipt hashes. Scientific freeze separately authenticates every payload file.'))
print('frozen',len(payload),'manifest',len(payload)+1)
