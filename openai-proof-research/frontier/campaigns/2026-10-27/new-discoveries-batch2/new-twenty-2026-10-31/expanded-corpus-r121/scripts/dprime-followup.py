import pathlib,subprocess,sys,runpy,json
D=pathlib.Path(__file__).resolve().parents[1]
for k in range(13,24):
 subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),f'dprime-{k}-3',sys.executable,'-I',str(D/'scripts/dprime.py'),str(k),'3'],check=True)
get=runpy.run_path(str(D/'scripts/fetch.py'))['get'];print(get(('potla-head.json','https://api.github.com/repos/Potla1995/hypergraphSuspension/commits/HEAD')))
h=json.loads((D/'sources/potla-head.json').read_text())['sha'];print(get(('potla-tree.json',f'https://api.github.com/repos/Potla1995/hypergraphSuspension/git/trees/{h}?recursive=1')))
