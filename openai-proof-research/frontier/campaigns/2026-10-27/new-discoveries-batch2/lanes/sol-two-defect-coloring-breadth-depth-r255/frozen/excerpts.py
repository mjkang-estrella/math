import pathlib,subprocess,re,sys
L=pathlib.Path(__file__).parent
for name in sys.argv[1:]:
 p=L/'frozen'/(name+'.pdf');q=L/(name+'.pdf.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);s=q.read_text();print('\n======',name,'======\n',s[:2200])
 for m in list(re.finditer(r'(?m)^\s*(?:Conjecture|Question|Problem|Theorem)\s+[\dA-Z]',s))[:18]:print(s[max(0,m.start()):m.start()+1100])
