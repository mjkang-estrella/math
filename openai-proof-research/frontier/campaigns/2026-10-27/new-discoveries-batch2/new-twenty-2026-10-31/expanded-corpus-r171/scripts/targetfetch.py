import pathlib,sys,json
exec(compile((pathlib.Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(pathlib.Path(__file__).parent/'fetch.py'),'exec'))
sha=json.loads((D/'sources/omega-head.json').read_text())['sha']
for p in ['D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.lean','Library/Combinatorics/ghafari2026transversals.md','Library/FiniteGeometry/braunbruegge2023facetsymmetricedgepolytope.md']:
 fetch('https://raw.githubusercontent.com/the-omega-institute/trureturing/'+sha+'/'+p,'prior-'+p.rsplit('/',1)[-1])
for aid in ['1105.4772']:
 fetch('https://arxiv.org/pdf/'+aid,aid+'.pdf')
for p in sorted((D/'sources').glob('*.pdf')):
 if p.read_bytes().startswith(b'%PDF') and not p.with_suffix('.txt').exists():
  import subprocess
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
