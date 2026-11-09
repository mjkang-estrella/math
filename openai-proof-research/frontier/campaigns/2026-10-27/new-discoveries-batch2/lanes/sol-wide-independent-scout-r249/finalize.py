from pathlib import Path
import hashlib,json,datetime,re
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
refs=[]; ids=['2512.04241','2511.22981','2511.13819','2510.26134','2509.26630','2508.20360','2312.16052','2311.13980','2310.18798','2512.19395','2512.18913','2512.15125','2512.09176']
for p in L.parent.glob('*/*'):
 if p.parent==L or p.name not in ('SCOUTING.md','SUMMARY.md','discovery.md','PROOF.md','STATUS.md') or p.stat().st_size>300000:continue
 before=h(p);data=p.read_text(errors='replace');assert before==h(p)
 refs.append(dict(path=str(p),sha256=before,exact_hits=[s for s in ids if s in data]))
(L/'history-references.json').write_text(json.dumps(refs,indent=2))
sources=[json.loads(a) for a in (L/'sources.jsonl').read_text().splitlines()]
for row in sources:assert h(Path(row['original']))==h(Path(row['copy']))==row['sha256']
freeze=json.loads((L/'freeze.json').read_text())
for row in freeze['references']:
 assert h(Path(row['copy']))==row['sha256']
 if row['kind']=='scientific':assert h(Path(row['original']))==row['sha256']
(L/'provenance.json').write_text(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='proposed proof; HOLD novelty/substantive review',sources=sources,history_reference_file='history-references.json',counts=dict(additional=9,total=39,next=40),guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',guard_limits=dict(AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230),procedural_limit='initial older-history scan only post-hashed; see FAILURES.md',chronology_limit='API omitted three IDs; PDF title-page versions retained'),indent=2))
files={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ('manifest.json','verification-receipt.json')}
(L/'manifest.json').write_text(json.dumps(dict(schema=1,sha256=files,excludes=['manifest.json','verification-receipt.json']),indent=2))
print('Finalized',len(files),'files;',len(sources),'scientific original/copy bindings unchanged')
