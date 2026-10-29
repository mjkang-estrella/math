import json,hashlib,gzip,sqlite3,re,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parent.parent
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
hist=json.loads((L/'history-receipt.json').read_text())
db=sqlite3.connect(L/'history.sqlite');originals=[]
for h,p in db.execute('select h,path from bodies'):
 if re.search(r'sol-fresh-source-discovery-r11[123]/(discovery|SUMMARY|progress|PROOF|review)[.]md$',p):originals.append([h,p])
dump('retained-r111-r113-science.json',originals)
# Reopen all actual isolation matches, and bind all aliases, without treating a listing as an attempted proof.
matches=[]
for i in range(4):matches +=json.loads((L/f'isolation-screen-{i}.json').read_text())['hits']
hs={j['sha256'] for j in matches};aliases=[]
with gzip.open(L/'history-aliases.jsonl.gz','rt') as f:
 for line in f:
  h,p=json.loads(line)
  if h in hs:aliases.append([h,p])
dump('isolation-matching-aliases.json',aliases)
reopened=[]
for i,j in enumerate(matches):
 p=R/j['path'];b=p.read_bytes();dest=f'sources/original-match-{i}.txt';(L/dest).write_bytes(b)
 reopened.append(dict(original=str(p),copy=dest,sha256=sha(b),same_as_scanned=sha(b)==j['sha256'],disposition='Catalog listing only, not an attempt' if 'games-list' in str(p) else 'Unrelated general-position survey bibliography, not isolation-game investigation'))
dump('original-reopen-receipts.json',reopened)
dump('provenance.json',dict(status='NO_ELIGIBLE_NOMINATION',credit=0,lane=str(L),counts_as_read=dict(additional=9,total=39,next=40),source_http=http,history=hist,isolation_screen=dict(unique_bodies=sum(json.loads((L/f'isolation-screen-{i}.json').read_text())['bodies'] for i in range(4)),matching_bodies=len(matches),aliases=len(aliases),all_dates=True,global_hit_cutoff=None,semantic_clearance=False),registry=dict(omega='e1ff281c3881e633b86be1072f049a778bdbdc1b',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',observation_utc='2026-10-29T23:09:12Z',delta='2108cd1f896d198a2137f61fdbad1cd72d660b18...e1ff281c3881e633b86be1072f049a778bdbdc1b',semantic_clearance=False,inherit='r130 registry-delta-receipt, r129/r130 qualified prior receipts; no re-download of historical intervals'),limitations=['No worldwide novelty claim','Lexical corpus only; omitted formats/oversized/role exclusions enumerated per shard','Current registry paths and retained original bodies are not generic semantic clearance','Journal source access status in http.jsonl; arXiv latest full bodies read','Shared scan as-read not transactional; mutable NEXT separate','No Lean, paper, acceptance, git, external messages, uploads or browser tabs'],checks=['games.py: 288 sampled graphs, not exhaustive','sustain.py: 5 disconnected path collections, not source proofs'],abandoned=['check.py weighted-bond graph checker prepared but never executed after public refutation hit','work.py inherited unused context/scan/retain/freeze modes were not invoked; only fetch, manifest, verify used'],failures=['Initial combined context tool read truncated: replaced by retained as-read context and structured/targeted reads','Initial broad Rall lightweight search produced irrelevant matches: rerun exact IDs/phrases','arxiv burning v2 web404, v1 obtained once; burning directions lacked a precise conjecture and dropped','DMTCS web fetch unavailable; separate public HTTP attempt retained, no bypass'],root_alone_adjudicates=True))
mutable={'sources/context-NEXT.md','sources/context-NEXT-outline.txt'}
dump('scientific-freeze.json',dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),files=[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted((L/'sources').iterdir()) if p.is_file() and str(p.relative_to(L)) not in mutable],mutable_context_excluded=sorted(mutable)))
print('science retained',len(originals),'isolation matches',len(matches),'aliases',len(aliases))
