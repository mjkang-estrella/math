import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));from fetch import get
for key,url in [('riordan-journal.pdf','https://pure.strath.ac.uk/ws/portalfiles/portal/86962771/Cheon_etal_LAA_2019_Riordan_graphs_II_spectral_properties.pdf'),('chromatic-resolution.pdf','https://arxiv.org/pdf/2504.00834'),('positroid-resolution.pdf','https://alco.centre-mersenne.org/item/10.5802/alco.475.pdf')]:print(get((key,url)),flush=True)
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
print(get(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')),flush=True)
o=json.loads((D/'sources/omega-root.json').read_text())
for row in o['tree']:
 if row['path'] in ['D5','Problems']:print(get(('omega-'+row['path']+'.json',row['url']+'?recursive=1')),flush=True)
