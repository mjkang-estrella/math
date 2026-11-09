from pathlib import Path
import gzip,resource,signal,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent
raw=gzip.decompress((L/'frozen/inputs/compression/steiner-7-5-0.bin.gz').read_bytes());n=24;full=16383
pack=lambda s:sum(v*64**i for i,v in enumerate(raw[s*n:(s+1)*n]))
meta=[]
for count in [256,1024,8191]:
 s='import PackedRows\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace PackedBenchmark'+str(count)+'\nopen Polyomino57.Diagonal.FiniteProof.Packed\n'
 for j in range(1,count+1):
  s+=f'theorem check{j} : mergeCheck 24 {pack(j)} {pack(full^j)} {pack(full)} = true := by decide\n'
 s+='end PackedBenchmark'+str(count)+'\n'
 (L/'dev'/f'Packed{count}.lean').write_text(s)
 meta.append(dict(module=f'Packed{count}',partitions=count,scalar_inequalities=count*n,full_mask=full,left_masks=[1,count],right_mask='16383 xor left',vertices=n,table_sha256=__import__('hashlib').sha256(raw).hexdigest()))
(L/'packed-benchmark-inputs.json').write_text(json.dumps(meta,indent=2)+'\n')
