import sys,json,hashlib,pathlib
R=pathlib.Path(__file__).resolve().parents[3]
O=R/'frontier/sources/i32_geometric_relativity_discovery'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
p=pathlib.Path(sys.argv[1]);p=p if p.is_absolute() else R/p
lines=p.read_text().splitlines(keepends=True)
a=int(sys.argv[2]) if len(sys.argv)>2 else 1
b=min(int(sys.argv[3]),len(lines)) if len(sys.argv)>3 else len(lines)
chunk=''.join(lines[a-1:b])
record={'path':str(p.relative_to(R)),'first':a,'last':b,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'passage_sha256':hashlib.sha256(chunk.encode()).hexdigest()}
log=O/'read-passages.json';data=json.loads(log.read_text()) if log.exists() else []
data.append(record);log.write_text(json.dumps(data,indent=2)+'\n')
print(f'{record["path"]}:{a}-{b}\n'+chunk)
