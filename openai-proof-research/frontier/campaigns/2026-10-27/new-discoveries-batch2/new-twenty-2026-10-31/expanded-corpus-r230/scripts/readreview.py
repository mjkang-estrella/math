import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
paths=[D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json',pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]
rows=[]
for p in paths:
 b=p.read_bytes();o=json.loads(b) if p.suffix=='.json' else None
 rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),keys=list(o) if isinstance(o,dict) else None))
(D/'inherited-read-receipts.json').write_text(json.dumps(rows,indent=2)+'\n')
# Preserve useful source excerpts for every record, not a claim of complete proof audit.
x=json.loads((D/'extracted.json').read_text());out=[]
for i,o in x.items():
 p=D/'sources'/(o['source_url'].rsplit('/',1)[-1]+'.txt');ls=p.read_text().splitlines();out.append('\n## '+i+' '+o['title']+'\n')
 hits=[j for j,l in enumerate(ls) if re.search('Conjecture|conjecture|conjectured',l)]
 for j in hits[-6:]:out.append('\n'.join(f'{k+1}: {ls[k]}' for k in range(max(0,j-1),min(len(ls),j+6))))
(D/'source-excerpts.txt').write_text('\n\n'.join(out)+'\n')
