import pathlib,runpy,json
L=pathlib.Path(__file__).resolve().parents[1];f=runpy.run_path(str(L/'scripts/fetch.py'))['fetch'];r=json.loads((L/'logs/lean-pool-path-screen.json').read_text())
for p in r['candidates']:f('https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+p)
