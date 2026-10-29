exec(open(__file__.replace('fetch3.py','fetch.py')).read().split('urls=')[0])
urls={
'he.pdf':'https://www.engineering.uwaterloo.ca/~q7he/Z_PDF_PS_Published/2021_Reprint_JAP_SCV.pdf',
'withdrawn-abs.html':'https://arxiv.org/abs/1802.08400',
'omega-current.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits?per_page=1',
'openai-current.json':'https://api.github.com/repos/openai/math/commits?per_page=1'}
exec('r=[]'+open(__file__.replace('fetch3.py','fetch.py')).read().split('r=[]')[1].replace("(b/'http.json')","(b/'http3.json')"))
subprocess.run(['pdftotext','-layout',str(b/'sources/he.pdf'),str(b/'sources/he.txt')],check=True)
