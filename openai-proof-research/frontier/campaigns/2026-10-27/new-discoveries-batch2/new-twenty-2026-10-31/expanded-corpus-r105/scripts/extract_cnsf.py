import re,html,pathlib
D=pathlib.Path(__file__).resolve().parents[1];s=(D/'sources/2606.03436.html').read_text();out=[]
for block in re.findall(r'<div[^>]*class="ltx_listingline"[^>]*>(.*?)</div>',s,re.S):
 block=re.sub(r'<span class="ltx_tag ltx_tag_listingline">.*?</span>','',block,flags=re.S)
 text=html.unescape(re.sub('<[^>]+>','',block)).replace('\xa0',' ')
 out.append(text.strip('\n').lstrip('\n ').rstrip())
# indentation is carried by ltx_lst_space spans; don't strip whole lines
out=[]
for block in re.findall(r'<div[^>]*class="ltx_listingline"[^>]*>(.*?)</div>',s,re.S):
 block=re.sub(r'^.*?</span>\s*','',block,count=1,flags=re.S)
 out.append(html.unescape(re.sub('<[^>]+>','',block)).replace('\xa0',' ').rstrip())
(D/'scripts/cnsf_source.py').write_text('\n'.join(out)+'\n');print(len(out))
