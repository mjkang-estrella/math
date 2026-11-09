import pathlib,hashlib,json,shutil
here=pathlib.Path(__file__).resolve().parent
batch=here.parent.parent
old=here.parent/'sol-zeckendorf-finite-abundance-tail-formal-r6'
files=[(old/p, 'inherited/'+p) for p in ['SUMMARY.md','runner.py','certify.py','run.sh','Audit.lean','Inventory.lean','pins.json','source-bindings.json','immutable-references.json','provenance.json','implementation-receipt.json','replay-receipt.json','verification-receipt.json','MANIFEST.json','Literal.lean','Terminal.lean','Law.lean','Cells.lean','Product.lean','Prefix.lean','Marks.lean','Boards.lean','Injection.lean','Abundance.lean','Tail.lean']]
files += [(here.parent/lane/name,'frozen/'+name) for lane,name in [('root-zeckendorf-finite-tail-disposition-r7','STATUS.md'),('root-zeckendorf-review-disposition-r2','FINITE-CONCENTRATION.md'),('sol-zeckendorf-mixing-formal-feasibility-r2','FINITE-CONCENTRATION-REVIEW.md')]]
files += [(batch/p,'administrative/'+p) for p in ['AGENTS.md','ledger.json','prior-campaign-context.json']]
files += [(batch.parents[3]/'AGENTS.md','administrative/ancestor-AGENTS.md')]
records=[]
for src,dst in files:
 data=src.read_bytes(); h=hashlib.sha256(data).hexdigest(); target=here/dst;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 assert hashlib.sha256(src.read_bytes()).hexdigest()==h==hashlib.sha256(target.read_bytes()).hexdigest()
 records.append(dict(original=str(src),copy=dst,sha256=h,size=len(data),administrative=dst.startswith('administrative/')))
(here/'bindings.json').write_text(json.dumps(records,indent=2)+'\n')
print('frozen',len(records),'files')
