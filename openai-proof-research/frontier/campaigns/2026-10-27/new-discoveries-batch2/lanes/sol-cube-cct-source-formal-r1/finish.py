from pathlib import Path
import hashlib,json,tarfile
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((L/'freeze.json').read_text())
for r in frozen:assert sha(Path(r['original']))==r['sha256']==sha(L/r['copy'])
(L/'before-after.json').write_text(json.dumps({'all_originals_and_copies_unchanged':True,'entries':frozen},indent=2)+'\n')
rep=json.loads((L/'fresh-replay/replay-receipt.json').read_text())
assert rep['source_endpoint_status']=='PROVED_N5'
for p in L.rglob('*'):
 if p.is_file() and p.suffix in ['.olean','.ilean','.c','.o']:p.unlink()
assert not list(L.rglob('*.olean'))
(L/'provenance.json').write_text(json.dumps({
 'scientific_inputs':'freeze.json; verified original and copy before reading and again after all proof work',
 'source':'Hemminger–Landesman–Yao, Peckness of Edge Posets, Order34(2017)441–463, DOI10.1007/s11083-016-9408-x, Definition1.4 and Question6.6',
 'source_chronology':{'received':'2015-03-18','accepted':'2016-09-01','published_online':'2016-10-06','arxiv_v1':'2015-01-19','arxiv_v2':'2017-12-10'},
 'published_pdf_sha256':sha(L/'frozen/sol-cube-cct-preliminary-review-r1/primary/published.pdf'),
 'access':'Reused frozen actual published primary PDF/text and lawful preliminary retrieval receipt. No network requests in this lane. No denied route retried. Old inaccessible historical intervals parked.',
 'novelty':'HOLD; source/formal PASS does not clear current registries, classical binary-code reconstruction or inaccessible historical bodies. Independent prior review remains the bounded evidence; no new worldwide priority claim.',
 'counts':{'additional':9,'total':39,'next':40,'changed':False},
 'resources':'helpers fixed AS/RSS512MiB CPU210 wall230; Lean serial -j1 -M2700 RSS2800MiB CPU210 wall230; no cap raises',
 'compiled_own_artifacts_removed':True,'fresh_replay':rep,
 'scope':'Only n=5 is formally proved. Negates universal Question6.6. No all-n formal theorem; no n<5/minimum classification; no claim about Conjecture1.3.'
},indent=2)+'\n')
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
print('Final manifest',len(files),'files; declarations',rep['actual_declaration_count'],'generated partial',rep['generated_partial_declarations'])
