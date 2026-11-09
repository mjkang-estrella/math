from research import *
queries={'bmv':'ti:"BMV conjecture" AND au:Stahl','shapiro':'ti:"B. and M. Shapiro"','qtspp':'ti:"q-TSPP" AND au:Koutschan'}
for k,q in queries.items():fetch(k+'.atom','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=3')
# Freeze positive alias-hit reports before reading excerpts.
for p in [L.parent/'sol-subsum-multiplicity-breadth-depth-r239'/'SCOUTING.md',L.parent/'sol-fresh-source-discovery-r59'/'discovery.md']:
 h=sha(p);d=L/'dedup-frozen'/p.parent.name/p.name;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(p.read_bytes());assert sha(d)==h==sha(p);log('sourcebindings.jsonl',dict(source=str(p),copy=str(d),source_sha256=h,text_sha256=h))
