import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'));from fetch import fetch
D=pathlib.Path(sys.argv[1]);sha=json.loads((D/'sources/the-omega-institute-trureturing-head/body').read_text())['sha']
for j,p in enumerate(['Problems/parry-string-attractor-minimum.md','Blueprint/D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.md','Blueprint/D5/S1/Words/Attractors/FiniteWordAttractors.md','Blueprint/D5/S1/Words/Attractors/PeriodicPrefixAttractors.md']):fetch('https://raw.githubusercontent.com/the-omega-institute/trureturing/'+sha+'/'+p,'omega-parry-body-'+str(j))
