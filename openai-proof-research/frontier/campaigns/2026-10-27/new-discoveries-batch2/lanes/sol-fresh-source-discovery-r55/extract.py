import pathlib,subprocess
P=pathlib.Path(__file__).resolve().parent
for name in ['published','basic','frame','progress-report']:
 subprocess.run(['pdftotext','-layout',str(P/'sources'/f'{name}.pdf'),str(P/'sources'/f'{name}.txt')],check=True)
