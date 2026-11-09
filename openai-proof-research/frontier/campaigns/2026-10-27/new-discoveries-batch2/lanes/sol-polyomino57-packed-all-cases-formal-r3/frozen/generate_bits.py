from pathlib import Path
import gzip,json,signal,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent
raw=gzip.decompress((L/'frozen/inputs/compression/steiner-7-5-0.bin.gz').read_bytes());n=24;full=16383
p=lambda s:sum(v*64**i for i,v in enumerate(raw[s*n:(s+1)*n]))
for count in [256,1024,8191]:
 s='import PackedBits\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BitsBenchmark'+str(count)+'\nopen Polyomino57.Diagonal.FiniteProof.Packed\n'
 s+='def pairs : List (ℕ × ℕ) := ['+','.join(f'({p(j)}, {p(full^j)})' for j in range(1,count+1))+']\n'
 s+=f'theorem checked : pairs.all (fun ab => decide ((slack 24 ab.1 ab.2 {p(full)} &&& {32*sum(64**i for i in range(24))}) = {32*sum(64**i for i in range(24))})) = true := by decide\n'
 s+=f'theorem fully_checked : checkedPairs 24 {p(full)} pairs = true := by decide\n'
 s+='end BitsBenchmark'+str(count)+'\n' 
 (L/'dev'/f'Bits{count}.lean').write_text(s)
