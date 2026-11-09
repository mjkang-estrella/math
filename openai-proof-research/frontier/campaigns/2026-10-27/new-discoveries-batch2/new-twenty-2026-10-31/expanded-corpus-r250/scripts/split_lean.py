import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];p=D/'lean';s=(p/'Endpoint.lean').read_text();o=json.loads((D/'matroid-certificate.json').read_text());f=lambda b:'{'+','.join(map(str,b))+'}'
base=s[:s.index('theorem exchange_0')];(p/'Bases.lean').write_text(base+'end CommonBasis332371\n')
for k in range(8):
 out='import Bases\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace CommonBasis332371\n'
 for i in range(10*k,min(10*k+10,76)):
  A=f(o['bases'][i]);out+=f'''theorem check_{i} : bases.all (fun b => (({A} : Finset V) \\ b).all (fun e =>
    (b \\ ({A} : Finset V)).any (fun f => decide (insert f (({A} : Finset V).erase e) ∈ bases)))) = true := by decide
'''
 out+='end CommonBasis332371\n';(p/f'Cases{k}.lean').write_text(out)
a=s.index('theorem exchange_checked');tail=s[a:];a=tail.index('\ntheorem exchange :');combined=tail[:a]
for i in range(76):combined=combined.replace(f'  · exact exchange_{i}\n',f'  · simpa only [Finset.all_eq_true, Finset.any_eq_true, decide_eq_true_eq] using check_{i}\n')
out='\n'.join(f'import Cases{k}' for k in range(8))+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace CommonBasis332371\n'+combined+tail[a:];(p/'Endpoint.lean').write_text(out)
