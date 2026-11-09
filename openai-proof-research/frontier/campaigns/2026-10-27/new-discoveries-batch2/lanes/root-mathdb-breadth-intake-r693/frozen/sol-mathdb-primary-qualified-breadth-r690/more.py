import pathlib
P=pathlib.Path(__file__).resolve().parent
for id,a,b in [('335423',7900,11300),('406505',6000,7900)]:
 print(id,a,b,(P/(id+'.txt')).read_text()[a:b])
