import pathlib,subprocess,re,json,sys,runpy
D=pathlib.Path(sys.argv[1]).resolve()
for p in (D/'sources').glob('*/body'):
 if p.read_bytes()[:4]==b'%PDF' and not p.parent.name.startswith('pdf-'):
  out=D/'outputs'/('text-'+p.parent.name+'.txt')
  subprocess.run(['pdftotext','-layout',str(p),str(out)],capture_output=True)
for label in ['dilates-correct','mbv-proof','group-vor','match-vor','factors-vor']:
 p=D/'outputs'/('text-'+label+'.txt');lines=p.read_text().splitlines()
 print('\n===',label,'===')
 for j,l in enumerate(lines):
  if re.search('Corollary 1.8|Conjecture 7.7|Theorem 7.14|Conjecture 1.3|Conjecture 5.1|Theorem 1.1',l):print('\n'.join(lines[max(0,j-3):j+25]))
print('pool',[(j+1,l[:300]) for j,l in enumerate((D/'sources/pool-projects-found/body').read_text().splitlines()) if re.search('grundy|zeckendorf|2008.08503|2007.12021|1708.01329|taxicab|katona|338753|347324|347642|336775',l,re.I)])
