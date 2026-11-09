# Scan a (possibly damaged) PDF's Flate streams for text fragments. Usage: python3 -I pdf_stream_scan.py <pdf> <out.txt>
import re, zlib, sys
data=open(sys.argv[1],'rb').read()
out=[]; n=0; ok=0
for m in re.finditer(rb'stream\r?\n', data):
    s=m.end(); e=data.find(b'endstream', s)
    if e<0: continue
    n+=1
    try: t=zlib.decompressobj().decompress(data[s:e]); ok+=1
    except Exception: continue
    if b'TJ' in t or b'Tj' in t:
        parts=re.findall(rb'\((.*?)(?<!\\)\)', t)
        out.append(b''.join(parts).decode('latin1'))
open(sys.argv[2],'w').write('\n=====\n'.join(out))
print('streams',n,'inflated',ok,'text streams',len(out))
