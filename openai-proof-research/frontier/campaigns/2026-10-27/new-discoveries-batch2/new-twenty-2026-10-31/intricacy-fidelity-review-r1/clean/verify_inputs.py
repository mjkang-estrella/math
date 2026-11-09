from pathlib import Path
import hashlib,json,sys
p=Path(__file__).resolve().parent
expected=json.loads((p/'input-bindings.json').read_text())
rows={f:{'expected':v,'actual':hashlib.sha256(Path(f).read_bytes()).hexdigest()} for f,v in expected.items()}
result={'pass':all(r['expected']==r['actual'] for r in rows.values()),'count':len(rows),'files':rows}
(p/('bindings-'+sys.argv[1]+'.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'pass':result['pass'],'count':len(rows)}))
assert result['pass']
