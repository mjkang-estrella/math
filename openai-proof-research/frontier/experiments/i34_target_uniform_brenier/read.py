import sys,pathlib,json,hashlib
root=pathlib.Path(__file__).resolve().parents[3]
s=root/'frontier/sources/i34_target_uniform_brenier'
p=root/sys.argv[1];lines=p.read_text().splitlines(keepends=True)
a=int(sys.argv[2]) if len(sys.argv)>2 else 1;b=min(int(sys.argv[3]),len(lines)) if len(sys.argv)>3 else len(lines)
t=''.join(lines[a-1:b]);q=s/'read-passages.json';log=json.loads(q.read_text()) if q.exists() else []
log.append(dict(path=str(p.relative_to(root)),start_line=a,end_line=b,sha256=hashlib.sha256(t.encode()).hexdigest(),note='Printed to research agent for semantic reading'))
q.write_text(json.dumps(log,indent=2)+'\n');print(t)
