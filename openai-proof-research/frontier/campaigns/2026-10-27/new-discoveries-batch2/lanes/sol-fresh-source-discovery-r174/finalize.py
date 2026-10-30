import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def h(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('provenance.json',dict(utc=now,lane=str(L),credit=0,counts=dict(additional=9,total=39,next=40),root_adjudicates=True,solo=True,context_role='archived snapshot only; no live invariant',helper_guard=dict(path=str(guard),sha256=h(guard.read_bytes()),AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,cap_raises=False),primary_records='http.jsonl',primary_hashes='source-hashes.json',public_bodies='public-body-provenance.json',history='history-receipt.json',scope='Two fresh exact source claims screened; no full eligible resolution; current/historical public-registry coverage incomplete.'))
save('failures.json',dict(utc=now,network=[dict(url='https://doi.org/10.54550/ECA2027V7S1R3',tool='web.open',error='not accessible via this tool',action='No retry; distinct publisher homepage located by public search and linked PDF fetched'),dict(url='https://blogs.gwu.edu/jblewis/research/',tool='web.open',error='502 Bad Gateway',action='No retry; unused search locator only')],process=[dict(action='native bounded cat of combined history/context',outcome='Output truncated at 232609 tokens; replaced by bounded reads and guarded parsed receipt; no evidence inferred from truncation'),dict(action='native rg hyper-abs.html.txt before extraction completed',exit=2,reason='file absent; sequential guarded extraction then actual read succeeded'),dict(action='duplicate covers source fetch launched alongside early screen',outcome='retrieved 200 but r108 duplicate discovered; unused bytes preserved; no investment')],denied_routes_retried=False,guard_runs=[dict(script='diagnostic.py 3 4 5 (initial no-arg identical science)',exit=0,peak_groupRSS=15257600,wall_seconds=2.2444522510049865),dict(script='diagnostic.py 6',exit=0,peak_groupRSS=57999360,wall_seconds=69.91744547698181)],limits='No 403/429/challenge encountered in this lane. Prior denied routes parked. Native bounded reads and apply_patch used as authorized; every Python/retrieval/extraction/hash/check command invoked under unchanged guard.'))
save('search-receipt.json',dict(utc=now,queries=['site.arxiv.org 2026 combinatorics Conjecture log-concave October','site.arxiv.org 2026 we conjecture permutations','A Permutation Avoidance Game with Reverse Replies conjecture','2602.22129 conjecture','2603.16004 proof reverse strategy','Nondegenerate Hypermatrix Koprowski Lewis product','Vatter Permutation classes arxiv 2015 1409','A combinatorial problem in geometry 1935 pdf','ECA2027V7S1R3','KOPROWSKI_LEWIS_COUPLED_DIGIT_BIJECTION'],primary_locators=['https://arxiv.org/abs/2603.16004','https://arxiv.org/abs/2602.22129','https://ecajournal.kms-ks.org/','https://arxiv.org/abs/1409.5159','https://www.numdam.org/item/CM_1935__2__463_0.pdf'],limits='Receipt records bounded public-search locators and search date, not exact search execution timestamps or saved search-result bytes. Actual primary HTTP retrieval timestamps/bytes in http.jsonl. Search absence and MathDB badges are not novelty evidence.'))
# Freeze scientific bytes; exclude recomputable diagnostic reports and integrity receipts.
excluded={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts:
  b=p.read_bytes();rows.append(dict(path=str(p.relative_to(L)),sha256=h(b),bytes=len(b)))
save('scientific-freeze.json',dict(utc=now,status='zero credit; unresolved full target',records=rows,context='local archived snapshot bytes only; do not compare to live campaign',excludes=sorted(excluded)))
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'} and '__pycache__' not in p.parts:
  b=p.read_bytes();rows.append(dict(path=str(p.relative_to(L)),sha256=h(b),bytes=len(b)))
save('finalmanifest.json',dict(utc=now,records=rows,excluded=['finalmanifest.json','manifest-verification.json'],selfhash=False))
print('frozen',len(rows),'manifest entries')
