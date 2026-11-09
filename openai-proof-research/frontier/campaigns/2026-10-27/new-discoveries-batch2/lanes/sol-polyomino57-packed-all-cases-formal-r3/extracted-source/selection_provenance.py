from generate_cases import *
import hashlib
rr=json.loads((L/'frozen/frozen/inputs/compression/verification.json').read_text())['receipts'];out=[]
for r in rr:
 if r['verified']!='potential-inequalities':continue
 a,b,e,n,k=(r[t] for t in ['a','b','e','vertices','groups']);file=L/f'frozen/frozen/inputs/compression/steiner-{a}-{b}-{e}.bin.gz';raw=gzip.decompress(file.read_bytes())
 best=min((m for m in range(1,1<<k) if all(v>=12 for v in raw[m*n:(m+1)*n])),key=lambda m:(m.bit_count(),m))
 candidate=best
 completed=set((L/'completed-modules.txt').read_text().splitlines())|{'C10_8_1Case','C10_10_1Case'}
 if f'C{a}_{b}_{e}Case' in completed:best=(1<<k)-1
 out.append(dict(best_data_candidate_mask=candidate,case=[a,b,e],vertices=n,original_groups=k,selected_mask=best,selected_group_positions=[i for i in range(k) if best>>i&1],selected_groups=best.bit_count(),frozen_compressed_sha256=hashlib.sha256(file.read_bytes()).hexdigest(),frozen_raw_sha256=hashlib.sha256(raw).hexdigest(),selection_scope='data-generation choice; no minimality or completeness claim is a logical premise'))
(L/'selection-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
