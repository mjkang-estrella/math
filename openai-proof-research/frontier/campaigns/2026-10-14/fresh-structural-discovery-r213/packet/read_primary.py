from pathlib import Path
import sys,json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r213/private/primary')
for arg in sys.argv[1:]:
 k,aa,zz=arg.split(':');a=int(aa);z=int(zz);p=R/(k+'.txt');b=p.read_bytes();assert 0<=a<z<=len(b)
 c=b[a:z];t=c.decode();page=1+b[:a].count(b'\f')
 print(f'--- PRIMARY {k} extraction bytes [{a},{z}) starts PDF page {page}; selected section only ---')
 print(t)
 with (R/'read-extents.jsonl').open('a') as f:f.write(json.dumps({'id':k,'extraction_sha256':hashlib.sha256(b).hexdigest(),'start':a,'end':z,'start_pdf_page_1based':page,'end_pdf_page_1based':1+b[:z].count(b'\f'),'mode':'semantic extraction reading','visual_limit':'not yet visually checked','truncation':'none at reader; output checked separately'})+'\n')
