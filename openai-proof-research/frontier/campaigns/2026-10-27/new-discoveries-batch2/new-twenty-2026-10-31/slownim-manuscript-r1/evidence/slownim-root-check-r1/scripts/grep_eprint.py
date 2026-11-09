import sys,tarfile,gzip,io,re
data=open(sys.argv[1],'rb').read()
pat=re.compile(sys.argv[2],re.I)
texts=[]
try:
    tf=tarfile.open(fileobj=io.BytesIO(data),mode='r:*')
    for m in tf.getmembers():
        if m.isfile() and m.size<5_000_000 and m.name.endswith(('.tex','.bbl')):
            texts.append((m.name,tf.extractfile(m).read().decode('utf8','replace')))
except tarfile.ReadError:
    try: texts.append(('single',gzip.decompress(data).decode('utf8','replace')))
    except OSError: texts.append(('raw',data.decode('utf8','replace')))
for name,t in texts:
    L=t.split('\n')
    for i,l in enumerate(L):
        if pat.search(l): print(f'{name}:{i+1}: {l[:300]}')
print('files',[n for n,_ in texts])
