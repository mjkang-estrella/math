import pathlib,sys
exec(compile((pathlib.Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(pathlib.Path(__file__).parent/'fetch.py'),'exec'))
fetch('https://arxiv.org/pdf/2010.07280','2010.07280.pdf')
import subprocess
subprocess.run(['pdftotext','-layout',str(D/'sources/2010.07280.pdf'),str(D/'sources/2010.07280.txt')])
