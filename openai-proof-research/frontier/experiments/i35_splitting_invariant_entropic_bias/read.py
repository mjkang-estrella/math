import pathlib,json,hashlib,sys
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i35_splitting_invariant_entropic_bias'
p=sys.argv[1]; lines=(R/p).read_text().splitlines(keepends=True);a=int(sys.argv[2]) if len(sys.argv)>2 else 1;b=min(int(sys.argv[3]),len(lines)) if len(sys.argv)>3 else len(lines)
t=''.join(lines[a-1:b]);out=S/'read-passages.json';log=json.loads(out.read_text()) if out.exists() else [];log.append(dict(path=p,start_line=a,end_line=b,sha256=hashlib.sha256(t.encode()).hexdigest(),note='Printed for semantic reading; no upstream truth audit'));out.write_text(json.dumps(log,indent=2)+'\n');print(t)
