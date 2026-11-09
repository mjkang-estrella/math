import pathlib,json,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/fetch.py').read_text().split("if __name__")[0],str(D/'scripts/fetch.py'),'exec'))
for i in sys.argv[1:]:
 o=json.loads((D/'extracted.json').read_text())[i];a=o['source_url'].split('/')[-1]
 fetch('https://arxiv.org/pdf/'+a,i+'.pdf')
 p=D/'sources'/ (i+'.pdf')
 if p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
