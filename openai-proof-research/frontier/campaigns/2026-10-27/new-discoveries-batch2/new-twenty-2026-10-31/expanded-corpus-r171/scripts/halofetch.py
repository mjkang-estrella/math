import pathlib,sys,subprocess
exec(compile((pathlib.Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(pathlib.Path(__file__).parent/'fetch.py'),'exec'))
fetch('https://arxiv.org/pdf/2302.07987','2302.07987.pdf')
subprocess.run(['pdftotext','-layout',str(D/'sources/2302.07987.pdf'),str(D/'sources/2302.07987.txt')])
