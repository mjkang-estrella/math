from pathlib import Path
import re,subprocess,json
P=Path(__file__).resolve().parent
pat=r'(^|[^0-9])357982([^0-9]|$)|2304[.]02230'
a=subprocess.run(['rg','-l',pat,'openai-proof-research/frontier/campaigns','-g','*.md','-g','*.json','-g','*.txt'],capture_output=True,text=True)
P.joinpath('duplicate-exact-id-filenames.txt').write_text(a.stdout)
for f in a.stdout.splitlines():
 if '/sol-fresh-source-discovery-r83/' in f:continue
 print(f)
 with open(f) as h:
  count=0
  for no,line in enumerate(h,1):
   if re.search(pat,line):print(str(no)+':'+line[:700]);count+=1
   if count==3:break
# record relevant source-body excerpts, with scope not catalog badges
spec=[('hansen.txt',[(20,90),(1100,1150)]),('arvind.txt',[(4230,4278)]),('cp.txt',[(598,610)]),('distance-prior.txt',[(290,338)]),('zagreb-classical.txt',[(106,169)]),('small-genus.txt',[(299,321)]),('hansen-closest.txt',[(1070,1120)])]
with P.joinpath('body-excerpts.txt').open('w') as o:
 for n,sections in spec:
  lines=P.joinpath('sources',n).read_text().splitlines();o.write('\nFILE '+n+'\n')
  for lo,hi in sections:
   for i in range(lo-1,min(hi,len(lines))):o.write(f'{i+1}: {lines[i]}\n')
