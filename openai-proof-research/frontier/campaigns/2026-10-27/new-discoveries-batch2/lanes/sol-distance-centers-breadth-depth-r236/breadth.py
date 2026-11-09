from research import *
print(fetch('https://arxiv.org/pdf/2312.07754v1','up23.pdf'))
p=freeze(L/'primary'/'up23.pdf');out=L/'primary'/'up23.txt';subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True);freeze(out)
print(out.read_text()[:48000])
