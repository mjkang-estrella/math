import json,hashlib,datetime,re,sys
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
pat=re.compile(r'pancake|prefix.?revers|golubyatnikov|2511[.-]16959|2610[.-]30892',re.I)
inherited=[]
rels=['sol-fresh-source-discovery-r168/history-qualification.json','sol-steiner-gp-offline-citation-closure-r4/review.md','sol-pendulum-investment-review-r3/body-coverage.json','sol-pendulum-investment-review-r3/research/registry-topic-screen.json','sol-pendulum-investment-review-r3/research/supplement-screen.json','sol-clique-corona-preliminary-review-r1/body-coverage.json','sol-clique-corona-preliminary-review-r1/registry-copy-receipt.json','sol-clique-corona-preliminary-review-r1/registry-current-receipt.json']
rels += [str(p.relative_to(L.parent)) for p in (L.parent/'sol-pendulum-investment-review-r3/research').glob('body-*.md')]
rels += ['sol-clique-corona-preliminary-review-r1/omega-current.md']
for i,rel in enumerate(rels):
 p=L.parent/rel;b=p.read_bytes();dest='sources/inherited-'+str(i)+p.suffix;(L/dest).write_bytes(b)
 inherited.append(dict(original=str(p),copy=dest,bytes=len(b),sha256=sha(b),body_alias_matches=bool(pat.search(b.decode(errors='replace'))),scope='Retained fixed evidence; unrelated body selection does not clear matching unread prefix-reversal bodies.'))
save('inherited-evidence.json',dict(utc=now(),records=inherited))
current=[]
for rel in ['sol-pendulum-investment-review-r3/research/blueprint.json','sol-pendulum-investment-review-r3/research/problems.json','sol-pendulum-investment-review-r3/research/openai-pinned-preprints-tree.json']:
 p=L.parent/rel;b=p.read_bytes();j=json.loads(b); rows=j.get('tree',j if isinstance(j,list) else [])
 hits=[x.get('path','') for x in rows if isinstance(x,dict) and pat.search(x.get('path',''))]
 current.append(dict(path=str(p),sha256=sha(b),hits=hits,truncated=j.get('truncated') if isinstance(j,dict) else None))
save('saved-current-path-screen.json',dict(utc=now(),records=current,body_limit='Matching paths not present among saved selected bodies remain unread. No GitHub retries.'))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
gh=sha(guard.read_bytes());assert gh=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
save('failures.json',dict(utc=now(),access_failures=[r for r in http if 'error' in r],scientific_failures=['Domination-polynomial lead is old r70/r78; stopped.','Bing first-word results ineffective; raw bytes retained.','Neighboring source shift conjectures already have current public proof.','Prime degree alone fails transitivity at (19,16,4).','Alternating containment does not imply symmetric at (13,12,4).','Odd-k parity obstruction at (8,5,3).'],limits=['Matching registry bodies unread; historical merge inventories and OpenAI current tree/body gaps explicit.','Babai1981 original theorem body unread; exact bound read in later actual research body.','No worldwide priority or substantive-adaptation clearance.'],extraction_warning='pdftotext reported font-type mismatch for pancake.pdf and original.pdf; usable complete text retained.'))
save('provenance.json',dict(utc=now(),lane=str(L),status='Full ordinary source proof supplied; eligibility HOLD; credit0',counts='9 additional /39 total,next40; no count mutation',source_target=dict(doi='10.46298/dmtcs.16975',arxiv='2511.16959v3',label='Conjecture5',printed_page=17,quantifiers='Every integer k>=2; maximum over ALL integer n>k+1 of all generating middle indices k<m<n'),sources=http,guard=dict(path=str(guard),sha256=gh,AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,unchanged=True,limits_raised=False,environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),sampling_limit='40ms sampling does not rule out unsampled RSS transients'),audit='r168/r167 indexes reused; qualified originals refreshed, generated echoes have counterpart qualification; r111–113 preserved',prior_limits=['Positive matching public registry paths, unread bodies.','Frozen plus saved current evidence only, no denied request repeated.','Historical merge and OpenAI gaps as offline closure r4.','Routine classical/source adaptation unresolved; no nomination as eligible result.'],forbidden_actions_performed=False,children=False,external_state_mutations=False))
exclude={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
science=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in exclude:
  b=p.read_bytes();science.append(dict(path=str(p.relative_to(L)),sha256=sha(b),bytes=len(b)))
save('scientific-freeze.json',dict(utc=now(),status='Scientific content frozen; full ordinary proof/eligibility HOLD',entries=science))
manifest=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}:
  b=p.read_bytes();manifest.append(dict(path=str(p.relative_to(L)),sha256=sha(b),bytes=len(b)))
save('finalmanifest.json',dict(utc=now(),entries=manifest,excluded=['finalmanifest.json (self)','manifest-verification.json (receipt)']))
print('frozen',len(science),'manifest',len(manifest),'saved current hits',[len(r['hits']) for r in current])
