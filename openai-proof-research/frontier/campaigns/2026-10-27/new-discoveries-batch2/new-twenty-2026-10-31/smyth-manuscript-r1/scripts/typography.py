from pathlib import Path
p=Path(__file__).with_name('paper.py');s=p.read_text();s=s.replace('import subprocess','import subprocess,re')
a="(R/'paper.ms').write_text(s)"
b=r'''def mathfix(t):
 return re.sub(r'\blambda\b','lamda',t).replace(' member ',r' "\(mo" ')
s=re.sub(r'\$([^$]*)\$',lambda m:'$'+mathfix(m[1])+'$',s)
s=re.sub(r'(?ms)^\.EQ\n(.*?)^\.EN',lambda m:'.EQ\n'+mathfix(m[1])+'.EN',s)
s=s.replace('U^m_n','$U sub n sup m$').replace('U^m','$U sup m$')
(R/'paper.ms').write_text(s)'''
s=s.replace(a,b);p.write_text(s)
