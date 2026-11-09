import pathlib,re,sys
D=pathlib.Path(sys.argv[1]);
for i in sys.argv[2:]:
 ps=sorted((D/'sources').glob('html-'+i+'v*/text.txt'));s=ps[-1].read_text();print('\nID',i)
 for term in ['Conjecture','Theorem 1.','γ','dominat','σ max','σ_max']:
  hits=list(re.finditer(re.escape(term),s));
  for m in hits[-2:]:print(s[max(0,m.start()-180):m.start()+2000])
