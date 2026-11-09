import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/exact.py').read_text();s=s.replace('range(5,10)','range(5,11)').replace('range(j+1,10)','range(j+1,11)').replace('range(1024)','range(2048)').replace('sa==sb==1023','sa==sb==2047').replace('n=10,pin_size=5','n=11,pin_size=5').replace("'concepts-search.json'","'concepts11-search.json'")
(D/'scripts/exact11.py').write_text(s)
