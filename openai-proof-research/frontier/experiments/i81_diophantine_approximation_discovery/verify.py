"""I81 offline READ-ONLY evidence verifier. No fetch, file write, or reseal code."""
from pathlib import Path
from collections import Counter
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i81_diophantine_approximation_discovery'
E=R/'frontier/experiments/i81_diophantine_approximation_discovery'
REPORT=R/'frontier/iterations/i81-diophantine-approximation-discovery.md'
def sha(data):return hashlib.sha256(data).hexdigest()
def read(p):return (R/p).read_bytes()
def check(ok,msg):
    if not ok:raise AssertionError(msg)
def run(args):
    p=subprocess.run(args,cwd=R,capture_output=True)
    check(p.returncode in (0,1) if args[0]=='rg' else p.returncode==0,repr(args[:3])+': '+p.stderr.decode(errors='replace'))
    return p.stdout
seal=json.loads((S/'seal.json').read_text())
if len(sys.argv)>1:
    check(len(sys.argv)==3 and sys.argv[1]=='--expect-seal-sha256','usage: verify.py [--expect-seal-sha256 HEX]')
    check(sha((S/'seal.json').read_bytes())==sys.argv[2],'seal differs from externally supplied digest')
actual={str(p.relative_to(R)) for root in (S,E) for p in root.rglob('*') if p.is_file()}
actual.add(str(REPORT.relative_to(R)));actual.remove(str((S/'seal.json').relative_to(R)))
check(actual=={x['path'] for x in seal['artifacts']},'owned path domain changed')
for x in seal['artifacts']:
    data=read(x['path']);check(sha(data)==x['sha256'] and len(data)==x['bytes'],'owned artifact changed: '+x['path'])
refs=json.loads((S/'immutable-references.json').read_text())
for x in refs:check(sha(read(x['path']))==x['sha256'],'immutable reference changed: '+x['path'])
mapname='frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'
rows=json.loads(read(mapname));requests=[json.loads(x) for x in read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()]
tree=json.loads((S/'ledgers/sources/preprints-tree.json').read_text());check(not tree['truncated'],'truncated tree')
blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
check(len(tree['tree'])==13223 and len(blobs)==10373 and len({x['path'].split('/')[1] for x in tree['tree']})==749,'tree totals')
check(len(rows)==10373 and len({x['path'] for x in rows})==10373 and {x['path'] for x in rows}==set(blobs),'search domain coverage')
check(Counter(x['kind'] for x in rows)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'search kind counts')
for x in rows:
    data=read(x['local']);check(sha(data)==x['sha256'],'search body changed: '+x['local'])
    if x['kind']=='corpus':
        check(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blobs[x['path']]['sha'],'corpus Git blob mismatch: '+x['path'])
check(len(requests)==1033 and len({x['path'] for x in requests})==1033,'outside request multiset')
check({x['path'] for x in requests}=={x['path'] for x in rows if x['kind']!='corpus'},'outside exact coverage')
for x in requests:
    data=read(x['local']);check(x['status']==200 and x['git_match'],'inherited failed response')
    check(sha(data)==x['sha256'],'outside original body hash')
    check(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blobs[x['path']]['sha'],'outside original Git hash')
    if 'extraction' in x:check(sha(read(x['extraction']['path']))==x['extraction']['sha256'],'outside extraction hash')
inv=run(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus']).decode().splitlines()
check(sorted(inv)==(S/'corpus-inventory.txt').read_text().splitlines(),'corpus exact inventory')
# Search multiset replay deliberately follows splitlines, including PDF form-feed continuations.
fam=json.loads((S/'family-search.json').read_text());got=[]
for k in range(0,len(rows),200):
    got.extend(run(['rg',*fam['flags'],fam['pattern'],*[x['local'] for x in rows[k:k+200]]]).decode().splitlines())
check(sorted(got)==(S/'family-search.txt').read_text().splitlines(),'complete family search multiset')
for meta,out in [('history-search-v2.json','history-search-v2.txt')]:
    d=json.loads((S/meta).read_text());got2=run(['rg',*d['flags'],d['pattern'],*d['files']]).decode().splitlines()
    check(sorted(got2)==sorted((S/out).read_text().splitlines()),'expanded history multiset')
# Initial history is replayed against the frozen ledger, replacing just the printed path prefix.
d=json.loads((S/'history-search-domain.json').read_text());files=[];rewrites=[]
for p in d['files']:
    snap=S/'ledgers'/p
    if p in seal['mutable_ledgers']:
        q=str(snap.relative_to(R));files.append(q);rewrites.append((q+':',p+':'))
    else:files.append(p)
got1=run(['rg','-n','-i','--no-heading',d['pattern'],*files]).decode()
for a,b in rewrites:got1=got1.replace(a,b)
check(sorted(got1.splitlines())==sorted((S/'history-search.txt').read_text().splitlines()),'initial history multiset')
# Title family and selected full-directory coverage.
scope=json.loads((S/'discovery-scope.json').read_text());import re
fams=sorted({x['path'].split('/')[1] for x in rows if re.search(scope['title_pattern'],x['path'].split('/')[1],re.I)})
check(fams==json.loads((S/'candidate-families.json').read_text()),'title search')
selected=[x for x in rows if x['path'].split('/')[1] in scope['relevant_families']]
check(selected==json.loads((S/'relevant-source-files.json').read_text()),'companion file domain')
passages=json.loads((S/'passages.json').read_text())
for p in passages:
    lines=read(p['path']).splitlines(keepends=True);data=b''.join(lines[p['first']-1:p['last']])
    check(sha(data)==p['sha256'],'passage mismatch: '+p['label'])
primary=[json.loads(x) for x in (S/'primary-requests.jsonl').read_text().splitlines()]
pdf_count=0
for p in primary:
    check(p.get('status')==200,'primary response failed');check(sha(read(p['local']))==p['sha256'],'primary body')
    if 'extraction' in p:
        e=p['extraction'];check(e['code']==0 and sha(read(e['local']))==e['sha256'],'primary text hash')
        replay=run(['pdftotext','-layout',str(R/p['local']),'-']);check(sha(replay)==e['sha256'],'primary PDF stdout replay');pdf_count+=1
for obs in json.loads((S/'version-observations.json').read_text()):
    text=read(obs['record']).decode();found=sorted(set(re.findall(r'(?:1507\.05697|2609\.26354|2408\.15403)v\d+',text)))
    check(found==obs['versions'],'version observation')
diag=run([sys.executable,'-B',str(E/'diagnostics.py')]);check(diag==(E/'diagnostics.json').read_bytes(),'exact diagnostic replay')
drift=[]
for p in seal['mutable_ledgers']:
    if (R/p).read_bytes()!=(S/'ledgers'/p).read_bytes():drift.append(p)
print(json.dumps({'evidence':'PASS','original_proof':'author proofs only; independent review pending','contribution':'TECHNICAL; no substantial nomination','owned_artifacts':len(actual),'immutable_references':len(refs),'pinned_blobs':len(blobs),'pdf_text_representatives':776,'outside_originals':len(requests),'passages':len(passages),'family_search_records':len(got),'primary_responses':len(primary),'primary_pdf_replays':pdf_count,'mutable_ledger_drift_informational':drift,'seal_sha256':sha((S/'seal.json').read_bytes())},indent=2,sort_keys=True))
