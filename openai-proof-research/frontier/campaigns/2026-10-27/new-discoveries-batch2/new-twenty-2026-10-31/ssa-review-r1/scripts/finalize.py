import pathlib,hashlib,json,datetime,gzip,shutil
D=pathlib.Path(__file__).resolve().parents[1];S=D.parent/'expanded-corpus-r104'
before=json.loads((D/'receipts/input-before.json').read_text());after={str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in S.rglob('*') if p.is_file()}
(D/'receipts/input-after.json').write_text(json.dumps(after,indent=2));changes=[p for p in before.keys()|after.keys() if before.get(p)!=after.get(p)]
ex={str(p.relative_to(D/'source-only')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (D/'source-only/SSA5').glob('*.lean')};assert all(h==after['formal/'+p] for p,h in ex.items())
(D/'receipts/hash-comparison.json').write_text(json.dumps({'date':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_count_before':len(before),'input_count_after':len(after),'changed_inputs':changes,'source_extraction_sha256':ex,'extraction_identical':True},indent=2));print('input changes',changes)
p=D/'logs/full-audit.log'
if p.exists():
 with p.open('rb') as a,gzip.open(str(p)+'.gz','wb',compresslevel=1) as b:shutil.copyfileobj(a,b)
 p.unlink()
