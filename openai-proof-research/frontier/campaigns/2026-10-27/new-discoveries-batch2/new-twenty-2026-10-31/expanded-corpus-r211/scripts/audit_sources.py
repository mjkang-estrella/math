import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];out={}
for p in (D/'sources').glob('*-abs.html'):
 a=p.name[:-9];s=p.read_text();start=s.find('Submission history');chunk=s[start:s.find('</div>',start)];out[a]={'versions_in_abs':sorted(set(re.findall(r'\[v(\d+)\]',s))),'history_html':chunk,'current_pdf_receipt':a+'.pdf.receipt.json'}
(D/'outputs/arxiv-versions.json').write_text(json.dumps(out,indent=2)+'\n')
# Cache manifests only, never execute source code from downloads.
receipts={p.name:json.loads(p.read_text()) for p in (D/'sources').glob('*.receipt.json')}
(D/'outputs/http-manifest.json').write_text(json.dumps(receipts,indent=2)+'\n')
r=json.loads((D/'outputs/registry-screen.json').read_text())
for k in ['leanpool-projects-pinned.yml','leanpool-candidates_discovered.yml','leanpool-candidates_decisions.jsonl','openai-preprints-tree.json','omega-D5-tree.json','omega-Problems-tree.json']:
 a=r.get(k,{});print(k,'count',a.get('count'),'truncated',a.get('truncated'),'hits',str(a.get('hits'))[:2000])
