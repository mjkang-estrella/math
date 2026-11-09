from intake import *
for a,name in [('2205.07457','digital-followup'),('https://amj.math.stonybrook.edu/pdf-Springer-final/020-0152.pdf','billiard-journal'),('https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i1p14/pdf/','beaton-journal')]:
 url=a if a.startswith('https') else 'https://arxiv.org/pdf/'+a
 if fetch(url,name+'.pdf')==200:subprocess.run(['pdftotext','-layout',str(L/'sources'/(name+'.pdf')),str(L/'sources'/(name+'.txt'))])
for i in [348340,348490,350758,351617,353828,353841,354421,354446,355735,356425,356517,356603]:
 d=json.loads((L/f'sources/{i}.jsonl').read_text());a=d['source_url'].split('/')[-1]
 if fetch('https://arxiv.org/pdf/'+a,f'{i}.pdf')==200:subprocess.run(['pdftotext','-layout',str(L/f'sources/{i}.pdf'),str(L/f'sources/{i}.txt')])
