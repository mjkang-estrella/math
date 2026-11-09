import pathlib,json,runpy
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get'];h=json.loads((D/'sources/potla-head.json').read_text())['sha']
for n in ['README.md','exportAdjLists.cpp','Cycles_through_00.txt']:
 print(get(('potla-'+n,f'https://raw.githubusercontent.com/Potla1995/hypergraphSuspension/{h}/{n}')),flush=True)
