f=P.parent/'expanded-corpus-r322/registry-screen.json'
b=f.read_bytes();print(b.decode());(P/'registry-prior-metadata.json').write_text(json.dumps(dict(path=str(f),sha256=hashlib.sha256(b).hexdigest(),parsed=json.loads(b)),indent=2))
