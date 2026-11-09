import pathlib,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(2,23,2):
 z=json.loads(subprocess.check_output([str(D/'outputs/squares'),str(n),'500']))
 if n<=10:
  S=[s for s in range(1<<n) if not(s&(s<<1)) and not(s&1 and s>>(n-1)&1)];v={0:1};seq=[1]
  for m in range(20):
   v={s:(-1)**s.bit_count()*sum(v.get(t,0) for t in S if not s&t) for s in S};seq.append(sum(v.values()))
  assert [x%z['prime'] for x in seq]==z['sequence'][:21]
  z['independent_exact_integer_transfer_check_m_0_to_20']=True
 (D/f'logs/squares{n}.log').write_text(json.dumps(z)+'\n');out.append({k:v for k,v in z.items() if k not in ['C','sequence']})
(D/'outputs/squares-validation.json').write_text(json.dumps(out,indent=2));print(out)
