from research import *
print(fetch('https://apcz.umk.pl/TMNA/article/view/47721/37305','tmna-full.html'))
print(fetch('https://arxiv.org/pdf/2609.11384v1','centers-new.pdf'))
print(fetch('https://arxiv.org/pdf/2502.06504v1','centers-2025.pdf'))
print(fetch('https://arxiv.org/pdf/2508.13016v1','cardinality.pdf'))
for p in list((L/'primary').glob('*.pdf')):
 q=freeze(p); out=L/'primary'/(p.stem+'.txt')
 r=subprocess.run(['pdftotext','-layout',str(q),str(out)],capture_output=True)
 if r.returncode==0:
  freeze(out)
  with (L/'text-bindings.jsonl').open('a') as f:f.write(json.dumps({'pdf':str(q),'pdf_sha256':sha(q),'text':str(out),'text_sha256':sha(out)})+'\n')
 else: print(r.stderr.decode())
