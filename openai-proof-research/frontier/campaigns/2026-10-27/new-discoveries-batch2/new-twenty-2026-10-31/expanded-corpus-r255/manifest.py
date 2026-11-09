import pathlib,json,hashlib,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;h=lambda b:hashlib.sha256(b).hexdigest()
rs={p.name:json.loads(p.read_text()) for p in sorted(L.glob('*.receipt.json'))}
(L/'source-receipts.json').write_text(json.dumps(rs,indent=2)+'\n')
(L/'SHA256SUMS').write_text(''.join(h(p.read_bytes())+'  '+p.name+'\n' for p in sorted(L.iterdir()) if p.is_file() and p.name!='SHA256SUMS'))
print('manifest files',len(list(L.iterdir())),'receipt count',len(rs))
