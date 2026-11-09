import sys,pathlib,json,subprocess
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'))
from fetch import get
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
todo=[('erdos-prior.md',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/Problems/erdos-deep-triple-classification-refutation.md'),('record-prior.md',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/Problems/chenkitaevzhang-2024-separable-record-peak-three.md'),('2610.12433.pdf','https://arxiv.org/pdf/2610.12433'),('steiner2025.pdf','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i2p30/pdf/'),('RecordTransport.lean',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/D5/S1/Words/Patterns/Separable/RecordTransport.lean')]
for x in todo:
 print(get(x),flush=True)
 if x[0].endswith('.pdf') and (D/'sources'/x[0]).exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/x[0]),str((D/'sources'/x[0]).with_suffix('.txt'))])
