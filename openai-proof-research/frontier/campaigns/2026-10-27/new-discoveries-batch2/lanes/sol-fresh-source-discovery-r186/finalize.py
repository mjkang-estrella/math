from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('guard-binding.json',dict(path=str(guard),sha256=sha(guard.read_bytes()),address_space_bytes=512*1024*1024,sampled_group_rss_bytes=512*1024*1024,cpu_seconds=210,wall_seconds=230,limits='Unchanged guard; sampled RSS does not rule out unsampled transients.'))
save('search-receipt.json',dict(recorded_utc=now(),method='Public web search/open, no browser. Search tool results are reconnaissance; HTTP primary bytes are independently preserved.',queries=[
'graph conjecture 2025 threshold graphs open problem extremal',
'conjecture 2024 independence polynomial trees maximum',
'conjecture discrete optimization 2025 graph structural',
'Counting Graphs with Vertex Cover Lokshtanov',
'counting graphs vertex cover subexponential labeled',
'conjecture 2025 dissociation trees extremal',
'conjecture 2024 connected maximal independent sets',
'New Upper Bounds on the Number of Maximum Independent Sets arxiv',
'Lokshtanov number of graphs cover counting',
'New Upper Bounds Levit independent sets 900',
'longest subsequences #lis #lds conjecture',
'exact counting labeled graphs independence number algorithm graphs with bounded independence number',
'counting triangle-free graphs exact algorithm labeled',
'Counting Graphs with Vertex Cover solution',
'Counting and Sampling Labeled Chordal Graphs arxiv',
'counting triangle-free graphs algorithm time',
'triangle-free graphs 2^ counting exact algorithm',
'counting graphs subquadratic exact',
'counting graphs vertex cover Lokshtanov -site:sciencedirect.com -site:d-nb.info'],
primary_result_urls=['https://drops.dagstuhl.de/entities/document/10.4230/DagRep.15.1.105','https://arxiv.org/abs/2308.09703','https://arxiv.org/abs/2410.22951'],
reconnaissance_urls=['https://arxiv.org/html/2610.22838v1','https://arxiv.org/abs/2608.16639','https://www.mdpi.com/2075-1680/14/12/900'],
failure=dict(url='https://www.mdpi.com/2075-1680/14/12/900',tool='web open',status=429,action='Stopped on first response; no retry, proxy or bypass.'),limits='No exhaustive citation graph, specialist database or full current public registry audit.'))
save('provenance.json',dict(utc=now(),lane=str(L),status='UNRESOLVED; zero full nominations',counts=dict(additional=9,total=39,next=40),selected=[dict(author='Daniel Lokshtanov',doi='10.4230/DagRep.15.1.105',section='4.4',printed_page=117,published='2025-10-02',scope='Exact labeled graph count with minimum vertex cover <=k in uniform 2^{o(n^2)} time; all positive integer n,k',primary='sources/report.pdf',chronology='Published question follows ESA2023 exact chordal and 2024 triangle-free approximation papers. No exact public resolution found in bounded search, not priority clearance.')],companions=[dict(arxiv='2308.09703v2',date='2024-10-03',body='sources/chordal-v2.pdf',published_body='sources/chordal.pdf',scope_limit='Chordal graphs only; evaporation relies on simplicial vertices.'),dict(arxiv='2410.22951v1',date='2024-10-30',body='sources/triangle-v1.pdf',scope_limit='Approximate counting. Theorem1.3 accuracy floor and runtime do not establish exact rounding.')],primary_receipts='http.jsonl',history='history-receipt.json',original_copies='original-copy-provenance.json',cached_public_bodies='cached-body-receipts.json',registry='registry-screen.json',registry_limits='Current heads/capped intervals/missing merge trees PARKED; no prohibited retrieval or reconstruction.',denied_inventory='inherited-r181-http.jsonl',prohibited_routes_respected=['GitHub API/raw/codeload/patch/diff','ScienceDirect','Google challenge','IEEE stamp11029606/10177210 418','OpenReview one-bit 403','d-nb.info/1264734433/34 429','SSRN4334390 403','r181 arxiv-search429 and author TLS failures'],classical_tools='Inclusion-exclusion and isolated-vertex binomial transform are uncredited helpers.',validation='checks.json',proof_gap='No global clique-overlap compression/evaluation bound; triangle-free slice alone unresolved.',external_actions_performed=False,lean=False,manuscript=False,children=False,root_owns=['review','investment','acceptance'],date_limit='Actual UTC from runtime, not environment date label.'))
save('primary-hashes.json',dict(utc=now(),records=[dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted((L/'sources').iterdir())]))
excluded={'scientific-freeze.json','finalmanifest.json','scientific-verification.json','manifest-verification.json'}
def entries(ex):return {str(p.relative_to(L)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in ex}
save('scientific-freeze.json',dict(utc=now(),exclusions=sorted(excluded),administrative_policy='Local captured snapshots hashed; live NEXT/ledger/prior context are mutable administrative files and not frozen.',files=entries(excluded)))
save('finalmanifest.json',dict(utc=now(),exclusions=['finalmanifest.json','scientific-verification.json','manifest-verification.json'],files=entries({'finalmanifest.json','scientific-verification.json','manifest-verification.json'})))
print('frozen',len(json.loads((L/'scientific-freeze.json').read_text())['files']))
