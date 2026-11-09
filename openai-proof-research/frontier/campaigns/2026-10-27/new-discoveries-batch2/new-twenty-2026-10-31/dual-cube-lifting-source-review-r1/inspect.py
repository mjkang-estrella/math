import re,hashlib,subprocess
exec((p/'read_sources.py').read_text().split('for name')[0])
for name in ['376322','376322-v1']:
 text=(p/(name+'-clean.txt')).read_text()
 print('\n',name,'DEFINITIONS',text[:10500])
 print('\nTHEOREM2',text[text.index('Theorem 2 .'):text.index('4 Optimized')])
 print('\nCONJECTURE',text[text.index('5 Concluding'):text.index('References')])
 print('FIG4 OBJECT',re.findall(r'<figure[^>]*id="S3.F4"[\s\S]*?</figure>',(a/'sources'/(name+'.html')).read_text())[:1])
for key in ['openai-head','leanpool-head']:
 s=(p/(key+'.html')).read_text();print(key,'currentOid',re.findall(r'"currentOid":"([a-f0-9]+)"',s))
for key in ['main-abs','companion-abs']:
 s=(p/(key+'.html')).read_text();print(key,re.findall(r'\[Submitted[^<]+|\[v[0-9]+\][\s\S]{0,180}|name="citation_[^"]+" content="[^"]+"',s))
res=subprocess.run(['pdftotext','-layout',str(p/'qin2022.pdf'),str(p/'qin2022.txt')],timeout=25,capture_output=True,text=True);print('PDFTEXT',res.returncode,res.stderr)
text=(p/'qin2022.txt').read_text();print('QIN2022 initial',text[:16500])
print('QIN compound passages')
for m in re.finditer(r'compound|Hamiltonian cycles|Theorem 3|Theorem 4',text,re.I):print(text[max(0,m.start()-400):m.start()+1200])
