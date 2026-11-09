# Extract .tex text from an untrusted arXiv e-print (gzip tar or gzip single file) into memory; write only .txt into the given fresh output dir.
import sys,tarfile,gzip,io,pathlib
src=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=False)
data=src.read_bytes()
try:
    tf=tarfile.open(fileobj=io.BytesIO(data),mode='r:*')
    for m in tf.getmembers():
        if m.isfile() and m.name.endswith(('.tex','.bbl')):
            t=tf.extractfile(m).read().decode('utf-8','replace')
            name=m.name.replace('/','__').replace('..','_')
            (out/(name+'.txt')).write_text(t); print(m.name,len(t))
except tarfile.ReadError:
    t=gzip.decompress(data).decode('utf-8','replace'); (out/'main.tex.txt').write_text(t); print('single',len(t))
