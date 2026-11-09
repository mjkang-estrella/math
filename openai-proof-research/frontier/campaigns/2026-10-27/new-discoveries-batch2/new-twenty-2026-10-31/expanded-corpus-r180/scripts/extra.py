import pathlib,runpy,json,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1];m=runpy.run_path(str(D/'scripts/fetch.py'));f=m['fetch']
urls={'2509.05069.pdf':'https://arxiv.org/pdf/2509.05069','2205.15810.pdf':'https://arxiv.org/pdf/2205.15810','super-proof.html':'https://probxiv.com/problems/super-total-local-antimagic-coloring-of-graphs-9','zero-sum-later.pdf':'https://dmtcs.episciences.org/14599/pdf','golay.html':'https://errorcorrectionzoo.org/c/golay','super-journal.pdf':'https://bica.the-ica.org/Volumes/103/Reprints/BICA2023-53-Reprint.pdf'}
for name,url in urls.items():
 p=D/'sources'/name
 if f(url,p) and name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
(D/'outputs/extra-receipts.json').write_text(json.dumps(m['receipts'],indent=2))
# Read inherited structured context in full, preserve hashes and all substantive dispositions without artifact hashes.
contexts=[D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']
for i,p in enumerate(contexts):
 b=p.read_bytes();o=json.loads(b)
 (D/'outputs'/f'context-{i}.json').write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'content':o},indent=2))
print('Contexts read and frozen')
r=json.loads((D/'outputs/registry-screen.json').read_text());print({k:v.get('head') for k,v in r.items() if isinstance(v,dict) and 'head'in v});print([(x['query'],x['response'].get('total_count') if x['response'] else None) for x in r['searches']]);print('pool files',len(r['pool_matches']))
