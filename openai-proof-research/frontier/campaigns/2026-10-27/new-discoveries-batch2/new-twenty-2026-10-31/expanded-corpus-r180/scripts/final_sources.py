import pathlib,runpy,json,subprocess
D=pathlib.Path(__file__).resolve().parents[1];m=runpy.run_path(str(D/'scripts/fetch.py'))
p=D/'sources/2010.01435.pdf'
if m['fetch']('https://arxiv.org/pdf/2010.01435',p):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
(D/'outputs/final-source-receipts.json').write_text(json.dumps(m['receipts'],indent=2))
