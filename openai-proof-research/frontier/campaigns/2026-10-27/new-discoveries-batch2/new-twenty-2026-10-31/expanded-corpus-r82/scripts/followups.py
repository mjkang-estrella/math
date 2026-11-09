from fetch import D,get
import subprocess
items=[('stern-journal.pdf','https://publi.math.unideb.hu/paper/1586/download/10_5486_PMD_2011_4922.pdf'),('schinzel.pdf','https://publi.math.unideb.hu/load_doc.php?p=1587&t=pap'),('ulas-catalogue.html','https://virt3.matinf.uj.edu.pl/users/272-maciej-ulas'),('stern-2019.pdf','https://arxiv.org/pdf/1909.10844'),('torsion-later.pdf','https://arxiv.org/pdf/2608.22285'),('farhi-later.html','https://www.worldscientific.com/doi/10.1142/S1793557114500028'),('containment-later.html','https://www.sciencedirect.com/science/article/pii/S0021869313003810'),('omega-lonely.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/40e572189e8b2852a6e9241e149bb27dab559dde/D5/S1/Phase/LonelyRunnerFourteenOfTwenty.lean')]
for key,url in items:
 print(get((key,url)),flush=True)
 if key.endswith('.pdf') and (D/'sources'/key).exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/key),str(D/'sources'/key).replace('.pdf','.txt')])
