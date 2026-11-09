import sys,tarfile,io,gzip
data=open(sys.argv[1],'rb').read(); name=sys.argv[2]; ranges=[tuple(map(int,r.split('-'))) for r in sys.argv[3:]]
tf=tarfile.open(fileobj=io.BytesIO(data),mode='r:*')
for m in tf.getmembers():
    if m.isfile() and m.name.endswith(name):
        L=tf.extractfile(m).read().decode('utf8','replace').split('\n')
        for a,b in ranges:
            for i in range(a-1,min(b,len(L))): print(f'{i+1}: {L[i]}')
            print('---')
