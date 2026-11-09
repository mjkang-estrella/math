import pathlib,json,hashlib,datetime
import verify
P=pathlib.Path(__file__).resolve().parent
result=verify.main();b=(P/'manifest.json').read_bytes()
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verification':result,'scope':'Integrity only; no mathematics/novelty acceptance','prior_failed_check':'First verification exit1: expected excluded receipt path was absent; placeholder created before final seal. Original inputs unchanged.'}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
