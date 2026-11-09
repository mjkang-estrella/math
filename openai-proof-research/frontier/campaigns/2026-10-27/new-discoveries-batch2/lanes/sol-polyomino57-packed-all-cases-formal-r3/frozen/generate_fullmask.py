from pathlib import Path
import gzip,json,signal,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent
raw=gzip.decompress((L/'frozen/inputs/compression/steiner-7-5-0.bin.gz').read_bytes());n=24;full=16383
p=lambda s:sum(v*64**i for i,v in enumerate(raw[s*n:(s+1)*n]))
mods=[];meta=[]
for k,start in enumerate(range(1,8192,1024)):
 end=min(start+1024,8192);mod=f'PackedFull{k}';mods.append(mod)
 s='import PackedBits\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+mod+'\nopen Polyomino57.Diagonal.FiniteProof.Packed\n'
 s+='def pairs : List (ℕ × ℕ) := ['+','.join(f'({p(j)}, {p(full^j)})' for j in range(start,end))+']\n'
 s+=f'theorem fully_checked : checkedPairs 24 {p(full)} pairs = true := by decide\n'
 s+='end '+mod+'\n';(L/'formal'/f'{mod}.lean').write_text(s);(L/'dev'/f'{mod}.lean').write_text(s)
 meta.append(dict(module=mod,first_left_mask=start,last_left_mask=end-1,right_mask='16383 xor left',rows=end-start))
s=''.join(f'import {m}\n' for m in mods)+'set_option autoImplicit false\nnamespace PackedFull\nopen Polyomino57.Diagonal.FiniteProof.Packed\n'
s+='def pairs : List (ℕ × ℕ) := '+' ++ '.join(m+'.pairs' for m in mods)+'\n'
s+=f'theorem coordinate_merge {{a b : ℕ}} (h : (a,b) ∈ pairs) : ∀ i < 24, digit {p(full)} i + 1 ≤ digit a i + digit b i := by\n'
s+='  simp only [pairs, List.mem_append] at h\n  rcases h with '+'((((((h | h) | h) | h) | h) | h) | h) | h'+'\n'
for m in mods:s+=f'  · exact checkedPairs_sound {m}.fully_checked h\n'
s+='end PackedFull\n';(L/'formal/PackedFull.lean').write_text(s);(L/'dev/PackedFull.lean').write_text(s)
(L/'fullmask-provenance.json').write_text(json.dumps(dict(case=[7,5,0],full_mask=full,vertices=24,table_sha256=__import__('hashlib').sha256(raw).hexdigest(),partitions=8191,scalar_merge_inequalities=8191*24,scope='all proper unordered partitions of full mask; local literal rows; not all union masks and not a geometric case',batches=meta),indent=2)+'\n')
