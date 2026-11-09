import pathlib,subprocess,json
L=pathlib.Path(__file__).resolve().parent
patterns={'shuffle':r'1412\.7488|Ayyer.{0,30}Schilling|random.to.random.{0,40}(poset|linear extension)', 'other':r'1412\.7408|1803\.10224|1001\.1571|2012\.15502|0607789|0508327|1412\.8682|1401\.2313|1706\.05230|2010\.01511|0908\.3473|Arouche|Juhnke|Polynomials Associated with Finite Markov'}
for k,q in patterns.items():
 r=subprocess.run(['rg','-n','-i','--glob','*.md','--glob','*.json',q,str(L.parents[4])],capture_output=True,text=True)
 lines=[x for x in r.stdout.splitlines() if str(L) not in x and not any(s in x for s in ['/administrative/','/frozen/','/inputs/','/science/'])]
 (L/(k+'-history.txt')).write_text('\n'.join(lines));print(k,'hits',len(lines));print('\n'.join(x[:1000] for x in lines[:25]))
