import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((D/'extracted.json').read_text());pat=re.compile(r'intervalclosed|signedcardinal|colbourn|subsquare|perfect.*divisib|klein.*bottle|suspension.*tree|glued.*poset|gluing.*poset|anastos|fabian|szab[oó]|three.*matching|matching.*multipli|chromatic.*homol|blaschke|self.*guard|ising.*map|sphere.*intersect|rigidity.*polytop|venn|pruesse|helme.guizon|bousquet|chaniotis|koerts|hoang|saxl|'+ '|'.join(list(rows)+list({r['source_url'].split('/')[-1] for r in rows.values()})),re.I)
out={'date':'2026-11-05','heads':{k:json.loads((D/f'sources/{k}-head.json').read_text())['sha'] for k in ['pool','omega','openai']},'scope_note':'Path screens do not amount to all-body semantic review. Global Omega/OpenAI trees are truncated; complete D5, Problems and preprints subtrees used. Exact positive hits inspected separately.','trees':{},'pool_text':{},'repository_searches':[]}
for name in ['pool-tree.json','omega-D5-tree.json','omega-Problems-fulltree.json','openai-preprints-fulltree.json']:
 p=D/'sources'/name;t=json.loads(p.read_text());out['trees'][name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':t['truncated'],'entries':len(t['tree']),'hits':[x['path'] for x in t['tree'] if pat.search(x['path'])]}
for p in (D/'sources').glob('pool-*'):
 if p.name.endswith(('.receipt.json','.json','.lean')):continue
 out['pool_text'][p.name]=[l for l in p.read_text().splitlines() if pat.search(l)]
for p in (D/'sources').glob('*search*.json.receipt.json'):
 out['repository_searches'].append(json.loads(p.read_text()))
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
for k,t in out['trees'].items():print(k,t['entries'],t['truncated'],len(t['hits']))
