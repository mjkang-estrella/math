from pathlib import Path
import json,math
D=Path(__file__).parent;p=D/'bounded-checks.json';r=json.loads(p.read_text());a=[0,1]
for _ in range(130):a.append(math.isqrt(2*(2*a[-1]+1)**2)//2)
r['failed_initial_convention']='Fractional-bit convention mismatches already at n=1 (recurrence 1 versus fractional bit 0). Preserved initial check.'
r['integer_bit_first_check']=[dict(n=n,recurrence_bit=a[2*n+1]-2*a[2*n-1],expected=math.isqrt(2*(1<<(2*(n-1))))%2) for n in range(1,65)]
r['integer_bit_first_all_match']=all(x['recurrence_bit']==x['expected'] for x in r['integer_bit_first_check']);p.write_text(json.dumps(r,indent=2)+'\n')
p=D/'dispositions.json';s=json.loads(p.read_text())
for x in s:
 if x['mathdb_id']==391007:x['technical_disposition']='Exact integer-square-root check: n=1 gives 1, whereas the first fractional bit is 0. With the integer bit counted first, all 64 checked bits match. This is a digit-index convention issue, not a refutation or a general recurrence for arbitrary algebraic numbers; no credit.'
p.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n')
p=D/'failures.json';s=json.loads(p.read_text());s['failed_calculations']=['391007 initial fractional-bit interpretation fails at n=1; shifted integer-first interpretation matches 64 bits. Both outputs retained.'];p.write_text(json.dumps(s,indent=2)+'\n');print(r['integer_bit_first_all_match'])
