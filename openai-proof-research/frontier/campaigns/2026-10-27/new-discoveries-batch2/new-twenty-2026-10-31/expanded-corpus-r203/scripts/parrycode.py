import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'));from fetch import fetch
D=pathlib.Path(sys.argv[1]);sha=json.loads((D/'sources/the-omega-institute-trureturing-head/body').read_text())['sha'];fetch('https://raw.githubusercontent.com/the-omega-institute/trureturing/'+sha+'/Blueprint/D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.scribe.cs','omega-parry-code')
