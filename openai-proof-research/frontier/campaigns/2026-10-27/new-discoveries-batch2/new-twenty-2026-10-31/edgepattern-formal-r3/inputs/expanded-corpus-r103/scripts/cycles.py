from pathlib import Path
import ctypes,json
D=Path(__file__).resolve().parents[1]
lib=ctypes.CDLL(str(D/'scripts/cycles.so'));lib.counts.restype=ctypes.POINTER(ctypes.c_uint64)
n=20;a=lib.counts(n,0);b=lib.counts(n,1)
bad=[[i,a[i],b[i]] for i in range(1,1<<n) if a[i]!=b[i]]
o=dict(n=n,subsets=(1<<n)-1,mismatches=bad,full_count=a[(1<<n)-1],exactness='uint64 safe: 19! < 2^64; Held Karp counts directed cycles with minimum anchor exactly once')
(D/'outputs/cycles.json').write_text(json.dumps(o,indent=2)+'\n');print(o)
