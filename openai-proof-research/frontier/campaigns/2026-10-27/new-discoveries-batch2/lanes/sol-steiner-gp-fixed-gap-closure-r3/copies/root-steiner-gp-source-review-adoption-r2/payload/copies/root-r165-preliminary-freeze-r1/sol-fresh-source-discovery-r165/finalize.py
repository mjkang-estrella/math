from pathlib import Path
import hashlib,json,datetime,re,gzip,os
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def entry(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b))
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
for h in http:
 if 'sha256' in h:assert sha((L/'sources'/h['name']).read_bytes())==h['sha256']
heads={n:json.loads((L/f'sources/{n}-head.json').read_text())['sha'] for n in ['omega','openai']}
delta=json.loads((L/'sources/omega-delta.json').read_text())
baseline=[]
for n in ['omega','openai']:
 p=L.parent/'root-edge-irregulator-final-freeze-r1'/f'{n}-tree.txt.gz'
 b=p.read_bytes();s=gzip.decompress(b).decode()
 pattern=re.compile(r'steiner.*(position|lexico)|klavzar|kuziak|peterin|\byero\b',re.I)
 baseline.append(dict(path=str(p),sha256=sha(b),hits=[x for x in s.splitlines() if pattern.search(x)]))
hist=json.loads((L/'history-receipt.json').read_text());supp=json.loads((L/'supplement-screen.json').read_text())
extra_pattern=re.compile(r'2105[.]08391|10[.]1007/s40314-021-01619-y|Steiner.general.position|Steiner.*monoton|monoton.*Steiner|false.twin.*Steiner|\bKlav[zž]ar\b|\bKuziak\b|\bPeterin\b|\bYero\b',re.I)
root=L.parents[5];aliases=[]
for p,h,n in hist['records']:
 b=(root/p).read_bytes()
 if extra_pattern.search(b.decode(errors='replace')):aliases.append(dict(path=p,sha256=sha(b),exact_target=bool(re.search(r'2105[.]08391|Steiner.general.position',b.decode(errors='replace'),re.I))))
save('alias-final.json',dict(pattern=extra_pattern.pattern,hits=aliases,whole_bodies=True,cutoff=None))
save('registry-screen.json',dict(utc=utc,heads=heads,omega_delta=dict(base='b62773edfb6a6f7806de09b593b2e3b6834685c7',commits=delta['total_commits'],files=len(delta['files']),paths=[x['filename'] for x in delta['files']]),baseline=baseline,
 current_problems=dict(entries=len(json.loads((L/'sources/omega-current-problems.json').read_text())['tree']),truncated=False),
 actual_bodies=['sources/outer.md','sources/mobile.md'],limits=['aa026->a19a and a19a->490f inherited 300-path caps persist','current contents endpoint1000 cap superseded by complete subtree','lexical paths not semantic absence; no exhaustive current body audit','mobile library is attribution only, not actual proof replay']))
save('provenance.json',dict(utc=utc,disposition='ZERO qualifying nominees; complete ordinary proofs recommended routine-source exclusion; independent eligibility not cleared',
 claims=[dict(source='Klavzar–Kuziak–Peterin–Yero2021, DOI10.1007/s40314-021-01619-y',label='Problem7.1',scope='universal monotonicity of maximum k-Steiner general position numbers',endpoint='49-vertex graph sgp2>=40>39>=sgp3; later sgp40>=40'),dict(label='Problem7.3',scope='universal sharpness of Theorem5.2',endpoint='sgp4(P3 composed with K2)=5>4')],
 primary_http_chronology=http,history=dict(original_records=len(hist['records']),changed_new=len(hist['changed_or_new']),supplement=len(supp),hits=len(hist['hits']),r111_r113=hist['r111_r113'],baseline=hist['base'],qualification=hist['qualification_sha256']),
 guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=512*1024**2,sampled_group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sampling_ms=40,unsampled_peaks_not_excluded=True),
 native_search=dict(saved_response_bytes=False,chronology='discovery searches preceded01:21:46UTC first source retrieval; exact timestamp not independently retained',queries=['graph conjecture Steiner general position','A Steiner general position problem lexicographic sharp','Steiner general position monotonicity','Steiner general position Problem7.1','Steiner general position non-monotone'],limitation='native web searches were not run through subprocess guard; primary downloads were guarded and hashed'),
 counts=dict(additional=9,total=39,next=40,credit=0),external_actions=False))
scientific=[p for p in L.rglob('*') if p.is_file() and (p.name in ['PROOF.md','discovery.md','checks.py','amplification.py','checks.json','amplification.json','run-checks.sh'] or (p.parent==L/'sources' and not p.name.startswith('history-')))]
save('scientific-freeze.json',dict(utc=utc,entries=[entry(p) for p in sorted(scientific)],status='ordinary science frozen; eligibility unreviewed'))
for p in scientific:p.chmod(0o444)
files=[p for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','manifest-verification.json']]
save('finalmanifest.json',dict(utc=utc,entries=[entry(p) for p in sorted(files)]))
manifest=json.loads((L/'finalmanifest.json').read_text());freeze=json.loads((L/'scientific-freeze.json').read_text())
for doc in [manifest,freeze]:
 for e in doc['entries']:
  p=L/e['path'];assert p.stat().st_size==e['bytes'] and sha(p.read_bytes())==e['sha256']
save('manifest-verification.json',dict(utc=utc,manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_entries=len(manifest['entries']),scientific_entries=len(freeze['entries']),verified=True))
print((L/'manifest-verification.json').read_text())
