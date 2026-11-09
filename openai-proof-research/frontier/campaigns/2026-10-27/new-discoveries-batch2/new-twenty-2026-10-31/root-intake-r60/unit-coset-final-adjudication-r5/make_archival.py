from pathlib import Path
import ast,textwrap
out=Path(__file__).resolve().parent
import json
items=json.loads((out/'archival-content.json').read_text())
pages=[];lines=[];y=785

def esc(t):return t.replace('\\','\\\\').replace('(','\\(').replace(')','\\)')
def put(t,size=11,font='F1',x=50):
    global y
    lines.append(f'BT /{font} {size} Tf 1 0 0 1 {x} {y} Tm ({esc(t)}) Tj ET')
    y-=13.5 if size==11 else 20
def endpage():
    global lines,y
    if not lines:return
    lines.append(f'BT /F1 9 Tf 1 0 0 1 50 26 Tm (ARCHIVAL CERTIFICATE | 340110 | NOT CREDITED | Page {len(pages)+1}) Tj ET')
    pages.append('\n'.join(lines));lines=[];y=785
put('A periodic-coset obstruction to',18,'F2')
put('unit acyclic matchings',18,'F2');y-=10
plain=[]
for name,t in items:
    if name=='page':endpage();continue
    plain.append(t)
    wrapped=textwrap.wrap(t,width=92 if name=='p' else 75,break_long_words=False)
    if name=='h' and y<120:endpage()
    for line in wrapped:
        if y<65:endpage()
        put(line,11 if name=='p' else 13,'F1' if name=='p' else 'F2')
    y-=7
endpage()
objs=[b'',b'<< /Type /Catalog /Pages 2 0 R >>',b'',b'<< /Type /Font /Subtype /Type1 /BaseFont /Times-Roman >>',b'<< /Type /Font /Subtype /Type1 /BaseFont /Times-Bold >>']
kids=[]
for p in pages:
    content=p.encode('ascii');idx=len(objs);kids.append(f'{idx} 0 R')
    objs.append(f'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 595 842] /Resources << /Font << /F1 3 0 R /F2 4 0 R >> >> /Contents {idx+1} 0 R >>'.encode())
    objs.append(f'<< /Length {len(content)} >>\nstream\n'.encode()+content+b'\nendstream')
objs[2]=f'<< /Type /Pages /Count {len(pages)} /Kids [{" ".join(kids)}] >>'.encode()
pdf=bytearray(b'%PDF-1.4\n');offsets=[0]
for i,obj in enumerate(objs[1:],1):
    offsets.append(len(pdf));pdf.extend(f'{i} 0 obj\n'.encode()+obj+b'\nendobj\n')
xref=len(pdf);pdf.extend(f'xref\n0 {len(objs)}\n0000000000 65535 f \n'.encode())
for off in offsets[1:]:pdf.extend(f'{off:010} 00000 n \n'.encode())
pdf.extend(f'trailer\n<< /Size {len(objs)} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n'.encode())
(out/'output/pdf/340110-archival.pdf').write_bytes(pdf)
(out/'output/pdf/340110-archival.txt').write_text('\n\n'.join(plain))
print('pages',len(pages))
