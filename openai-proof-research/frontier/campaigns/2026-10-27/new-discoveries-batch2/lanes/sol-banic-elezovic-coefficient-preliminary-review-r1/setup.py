import pathlib,hashlib,json,shutil,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent; C=L.parent/'sol-wide-analysis-geometry-mechanisms-r261'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
(L/'administrative').mkdir(exist_ok=True); (L/'science').mkdir(exist_ok=True)
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
 if p.exists(): shutil.copyfile(p,L/'administrative'/p.name)
rows=[]
for p in [C/'PROOF.md',C/'exact.py',C/'lattice.py',C/'FAILURES.md',C/'provenance.json',C/'chronology.json',C/'access.json',C/'primary/2610.17046.pdf',C/'texts/2610.17046.txt',C/'primary/2610.17046-abs.html',C/'primary/author.html',C/'primary/prior.html',L.parent/'root-banic-elezovic-triage-r1/STATUS.md']:
 a=h(p); q=L/'science'/(a[:16]+'-'+p.name); shutil.copyfile(p,q);q.chmod(0o444)
 assert a==h(p)==h(q)
 rows.append(dict(original=str(p),copy=str(q),sha256=a))
(L/'bindings.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
