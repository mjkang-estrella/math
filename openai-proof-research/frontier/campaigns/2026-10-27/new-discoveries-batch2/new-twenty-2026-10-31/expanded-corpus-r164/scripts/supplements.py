import pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/fetch.py').read_text().split("if __name__")[0],str(D/'scripts/fetch.py'),'exec'))
for a in ['2611.00572','1805.03456','2011.13110','2011.02175','2411.05720']:
 fetch('https://arxiv.org/pdf/'+a,'prior-'+a+'.pdf')
 p=D/'sources'/('prior-'+a+'.pdf')
 if p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
