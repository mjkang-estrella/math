# Chunked extension g8 -> canonical 9-vertex graphs for parents with index in [lo,hi); output a chunk file.
import sys, pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent)); from graphgen import extend
lo,hi=int(sys.argv[1]),int(sys.argv[2]); d=pathlib.Path(sys.argv[3])
gs=[tuple(map(int,l.split())) for l in (d/'g8.txt').read_text().split('\n') if l.strip()][lo:hi]
res=extend(gs,9)
(d/f'g9.part{lo:05d}.txt').write_text('\n'.join(' '.join(map(str,g)) for g in sorted(res))+'\n')
print(lo,hi,len(res))
