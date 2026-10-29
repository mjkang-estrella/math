import json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
science=[p for p in (L/'sources').iterdir() if p.name.startswith(('ti-','two-total','source-p'))]
dump('source-lock.json',dict(frozen_at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),scope='Scientific source bytes/derived extraction, distinct from mutable coordination snapshot',files=[dict(path=str(p.relative_to(L)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(science)]))
dump('provenance.json',dict(lane=L.name,credit=0,counts=dict(additional=9,total=39),status='NO_FULL_PROOF_NO_NOMINEE',source=dict(authors=['Teresa W. Haynes','Michael A. Henning'],title='Augmenting graphs to partition their vertices into a total dominating set and an independent dominating set',doi='10.7494/OpMath.2025.45.2.179',statement='Conjecture6.1 printed p192; equivalent7.4 p196',url='https://www.opuscula.agh.edu.pl/vol45/2/art/opuscula_math_4510.pdf'),guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=536870912,sampled_group_RSS_bytes=536870912,cpu_seconds=210,wall_seconds=230,nominal_poll_ms=40,BLAS_threads=1),science='source-lock.json',context='context-receipts.json',registry='registry-coverage.json',history='screen-receipt.json',checks='check-results.json',failures=['Initial context output truncation','Initial nonexistent lane lookup','Long excluded-record output truncation','Raw factorial fresh-coverage output truncation; corrected by bounded parse'],external_mutations=False,children=False,lean=False,paper=False,proof_file=False,limits='No full mathematical or semantic prior-art clearance; selected original/closest bodies only. No worldwide absence or priority claim.'))
dump('search-receipts.json',dict(date_utc='2026-10-29',provider='web search tool',queries=['graph theory conjecture 2025 independent domination product','combinatorial optimization open question 2025 submodular polynomial conjecture','TI-augmentation conjecture','Haynes Henning cti augmentation 2026','Augmenting graphs to partition conjecture proof','Graphs whose vertex set 543 563 Haynes Henning pdf','TI-augmentation excluding source routes','Augmenting a graph of minimum degree2 pdf'],primary_urls=['https://www.opuscula.agh.edu.pl/vol45/2/art/opuscula_math_4510.pdf','https://www.opuscula.agh.edu.pl/vol44/4/art/opuscula_math_4426.pdf','https://people.computing.clemson.edu/~goddard/papers/augmentTwoTotal.pdf'],limit='Search responses are leads only. Exact HTTP source bytes/hashes saved in http.jsonl; search HTML/result bytes not saved.'))
excluded={'finalmanifest.json','manifest-verification.json'}
files=[p for p in L.rglob('*') if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts]
manifest={str(p.relative_to(L)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(files)}
dump('finalmanifest.json',manifest)
errors=[name for name,rec in manifest.items() if sha(L/name)!=rec['sha256'] or (L/name).stat().st_size!=rec['bytes']]
source=json.loads((L/'source-lock.json').read_text());errors += [x['path'] for x in source['files'] if sha(L/x['path'])!=x['sha256']]
assert not (L/'PROOF.md').exists()
assert json.loads((L/'check-results.json').read_text())['failed_route_witnesses']['strict_local_descent']['global_optimum']==2
dump('manifest-verification.json',dict(status='PASS' if not errors else 'FAIL',manifest_sha256=sha(L/'finalmanifest.json'),files=len(manifest),source_files=len(source['files']),errors=errors,scope='Post-write content/size and scientific-lock verification; manifest and detached verifier excluded from self inventory.'))
print(json.dumps(json.loads((L/'manifest-verification.json').read_text())))
assert not errors
