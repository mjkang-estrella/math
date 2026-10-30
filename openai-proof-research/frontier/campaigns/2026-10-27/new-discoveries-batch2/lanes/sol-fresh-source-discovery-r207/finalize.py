from pathlib import Path
import hashlib,json,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(L/'guard-copy.py').write_bytes(guard.read_bytes())
bindings=[dict(original=str(guard),copy='guard-copy.py',sha256=sha(guard))]
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
bindings += [r['binding'] for r in http if 'binding' in r]
bindings += json.loads((L/'registry-binding.json').read_text())
for x in bindings:assert sha(Path(x['original']))==sha(L/x['copy'])==x['sha256']
save('scientific-bindings.json',bindings)
save('scientific-before-after.json',dict(utc=now,status='PASS',before='Each HTTP source binding verified immediately after download and before extraction/body reading; work.py bind()',after='All scientific originals/copies rechecked by finalize.py; separate verify.py repeats after manifest',pairs=len(bindings)))
run=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,check=True)
(L/'checks.json').write_text(run.stdout);(L/'checks.stderr').write_text(run.stderr)
save('coverage-receipt.json',dict(utc=now,qualified_original_paths=1541,changed_new=9,inherited_aliases=2576,qualified_source_matches=0,inherited_source_matches=0,original_r111_113_retained=True,history='point-in-time reference snapshots; unchanged snapshot references reused, no recursive copying or equality-only qualification',current_search='Three subject lists, bounded title search returning source and predecessor',registry='Pinned October 8 catalog/tree only; no current complete authenticated head or bodies',gaps=['Actual predecessor journal body not separately read','Other citing literature not exhaustive','Current complete public registry/history unavailable','Historical registry caps and parked intervals remain qualified gaps'],prohibited_routes_attempted=False,worldwide_novelty_claim=False))
save('source-coverage-receipt.json',dict(utc=now,relied_bodies={'dim.pdf':'Definitions 2.1/4.1, Section 3 comparisons, Lemma 4.12 full proof, Lemma 4.14, Theorem 4.17 combined scales/allocation/gluing, Further Work Question 1','banaji.pdf':'Theorem B; Theorem 2.6 cover conversion passages; full Theorem 3.11 and Corollary 3.13','comp.pdf':'Section 6 Theorem 6.1, especially complete lower covering argument, Further Work'},unused=['cos.pdf','sep.pdf','survey.pdf'],reconnaissance=['chat.pdf','vseq.pdf','mah.pdf'],limits='No audit of all proofs in all downloaded papers; extraction font warning retained in FAILURES.md',http='http.jsonl'))
save('chronology.json',dict(utc=now,target=dict(arxiv='2610.35834v1',submitted='2026-10-26T17:52:03Z',history='only v1 in obtained current abstract',journal=None),classical=dict(doi='10.54330/afm.120529',received='2021-12-04',revised='2022-04-04',accepted='2022-04-27',published='2022-07-04',pages='939–960'),predecessor=dict(arxiv='2412.12999v3',versions=['2024-12-17T15:23:54Z','2025-10-30T19:55:02Z','2025-11-16T07:19:42Z'],journal_doi='10.1017/prm.2026.10162',journal_body='not separately authenticated')))
save('provenance.json',dict(utc=now,status='UNRESOLVED; zero nominations',lane=str(L),counts=dict(additional=9,total=39,next=40),target='Angelini2610.35834v1 Further Work Question1',primary_bytes='sources/',frozen_working_copies='frozen/',source_hashes_urls_utc='http.jsonl',scientific='scientific-bindings.json; scientific-before-after.json',history='qualified-original-index.json; alias-refresh.json; indexes/; changed/',administrative='administrative/ ledger/NEXT/context are snapshots only',checks='checks.py; checks.json',failures='FAILURES.md',limits='coverage-receipt.json; source-coverage-receipt.json',manifest_exclusions=['finalmanifest.json','verification-receipt.json']))
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'finalmanifest.json','verification-receipt.json'}}
save('finalmanifest.json',dict(utc=now,algorithm='SHA256',exclusions=['finalmanifest.json','verification-receipt.json'],files=files))
print(json.dumps({'files':len(files),'scientific_pairs':len(bindings),'checks':json.loads(run.stdout)}))
