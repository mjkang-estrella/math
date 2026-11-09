import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];pat=re.compile(r'mourre|lagrangian|spectral.?width|hanson|localiz.*paley|queen|sum.?difference|ted.?s.?polytope|directed.?neigh|matching.*descent|descent.*matching|ruzsa|ovoid|hypertree|super.?standard|chain.?type|subgraph.?arrange|all.?genus|braid.?class|weingarten|procesi|translated.?promotion|markov.?unique|overpartition',re.I);out={}
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 b=p.read_bytes();o=json.loads(b);out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'truncated':o.get('truncated'),'hits':[e['path'] for e in o.get('tree',[]) if pat.search(e['path'])]}
(D/'outputs/registry-target-rescreen.json').write_text(json.dumps(out,indent=2)+'\n')
for p,o in out.items():print(pathlib.Path(p).name, len(o['hits']));print('\n'.join(sorted({s.split('/')[0] if 'preprints' in p else s for s in o['hits']})))
