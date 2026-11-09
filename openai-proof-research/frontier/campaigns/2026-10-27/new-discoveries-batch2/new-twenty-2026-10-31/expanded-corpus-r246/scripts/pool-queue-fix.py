import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];q=json.loads((D/'queue-pool.json').read_text());h=json.loads((D/'sources/leanpool-head.json').read_text())['sha'];q.append(('leanpool-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/'+h+'/projects.yml'));(D/'queue-pool-full.json').write_text(json.dumps(q))
