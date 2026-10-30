from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
hist=json.loads((L/'history-receipt.json').read_text())
retained={}
for k in [111,112,113]:
 rows=[r for r in hist['records'] if f'/sol-fresh-source-discovery-r{k}/' in r[0] and '/core/' not in r[0]]
 assert rows;retained[str(k)]=rows
save('retained-originals.json',retained)
copies=json.loads((L/'cached-copy-provenance.json').read_text())
expected={'cached-Blueprint--D5--S3--Analytic--KummerRatio--Result.md':'f2deee754b50f7c334928401cf65d1fa664d7cb6','cached-Blueprint--D5--S3--Analytic--Chebyshev--SnakeChebyshevExpansionRefutation.md':'d930c58dde4189ce04717dcfb79ea16848310223'}
matches=[]
for n,h in expected.items():
 r=next(r for r in copies['records'] if r['copy']=='sources/'+n);assert r['git_blob_sha1']==h;matches.append([n,h])
save('registry-body-match.json',dict(utc=now,matches=matches,meaning='Cached actual bodies match blob objects in inherited registry trees; no current HEAD claim.'))
save('primary-hashes.json',dict(utc=now,records=[[str(p.relative_to(L)),sha(p.read_bytes()),p.stat().st_size] for p in sorted((L/'sources').iterdir()) if p.is_file()]))
g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('guard-binding.json',dict(path=str(g),sha256=sha(g.read_bytes()),AS_bytes=512*1024*1024,group_sampledRSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,unchanged=True))
save('failures.json',dict(retrieval=[],checks=[],administrative_probes=['Initial r178 directory listing absent before creation.','REPORT.md absent in old Euler review; actual review.md read.'],superseded=['First exploratory registry-screen output overwritten; final union retained.'],access_limits=['No denied routes retried; global/current and historical registry completeness remains PARKED.']))
save('provenance.json',dict(utc=now,lane=str(L),credit=0,baseline=dict(additional=9,total=39,next=40),targets=[dict(id='2507.01353v1 / 10.1007/s00454-026-00870-6',statement='Conjecture7.2(2)',decision='campaign duplicate r47; not reopened'),dict(id='0902.3073v1 / 10.1016/j.jmaa.2009.10.057',statement='unnumbered conjecture after Theorem4, both rays and gamma endpoints',decision='exact cached public resolution'),dict(id='2312.07754v1 / 2504.04845v1',statement='Nikolov snake positivity / Conjecture7.1',decision='exact cached public refutation; independently checked')],history=dict(records=len(hist['records']),changed_new=len(hist['changed']),missing=len(hist['missing']),qualification='inherited r175/r174/r173/r170; original r111-r113 retained; conservative added echoes; lexical only'),primary_versions=dict(karp='v1 2009-02-18; actual published author copy online2009-10-24, issue2010',up24='v1 2025-04-07',snake2023='v1 2023-12-12',snakeII='v1 2012-10-29',radon='cached v1 and actual 2026-09-07 VoR'),cached_public=dict(head=copies['clone_head'],first_publication_commits='not reconstructed',receipt='cached-copy-provenance.json'),access='http.jsonl; all fresh downloads200; repository network and denied routes not attempted',checks='checks.py/checks.json exact prior-certificate checks; written interval bridge in discovery.md',external_actions=False,children=False,lean=False,manuscript=False,shared_edits=False,context='archival administrative only',guard='guard-binding.json'))
excluded=['finalmanifest.json','manifest-verification.json','scientific-verification.json']
save('finalmanifest.json',dict(utc=now,records=[[str(p.relative_to(L)),sha(p.read_bytes()),p.stat().st_size] for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded],exclusions=excluded,reason='Manifest self and separately generated verification receipts cannot self-hash. No scientific payload is excluded.'))
print(json.dumps(dict(finalized_utc=now,manifest_records=len(json.loads((L/'finalmanifest.json').read_text())['records']),retained_old_lanes=list(retained))))
