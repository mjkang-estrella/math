import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent
sources=list((L/'sol-mathdb-ordinal-balls-preliminary-review-r526').rglob('*'))
sources += [L/'root-mathdb-stack-review-intake-r527'/n for n in ['manifest.json','verification-receipt.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','active-breadth-reservations.json','candidate-briefs.json','routing-queue.jsonl']]
sources += [L/'pi-mathdb-full-corpus-inventory-r301/manifest.json']
rows=[]
for src in sources:
 if not src.is_file():continue
 dst=P/'frozen'/src.relative_to(L);dst.parent.mkdir(parents=True,exist_ok=True);b=src.read_bytes();dst.write_bytes(b)
 rows.append({'original':str(src),'copy':str(dst),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n');print('frozen',len(rows))
