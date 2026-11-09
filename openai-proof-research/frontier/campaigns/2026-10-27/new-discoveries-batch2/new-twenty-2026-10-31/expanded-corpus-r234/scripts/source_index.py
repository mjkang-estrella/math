import json,pathlib,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1]
receipts={p.name:json.loads(p.read_text()) for p in (D/'sources').glob('*.receipt.json')}
(D/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
for tag in ['openai','pool']:
 tree=json.loads((D/f'sources/{tag}-tree.body').read_text());pat=re.compile('hurlbert|universal.*cycl|permutation.*cycl|walk.*matrix|shuffle|Haros|Macchia',re.I)
 print(tag,tree['sha'],'truncated',tree.get('truncated'))
 rows=[x['path'] for x in tree['tree'] if pat.search(x['path'])]
 print('\n'.join(rows[:35]));(D/f'notes/{tag}-target-paths.json').write_text(json.dumps(rows,indent=2))
