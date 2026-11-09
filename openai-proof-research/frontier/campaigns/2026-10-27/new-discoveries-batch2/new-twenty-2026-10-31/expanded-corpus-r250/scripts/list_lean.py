import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];p=D/'lean';o=json.loads((D/'matroid-certificate.json').read_text());f=lambda b:'{'+','.join(map(str,b))+'}'
s=(p/'Bases.lean').read_text();s=s.replace('def bases : Finset (Finset V) := {','def baseList : List (Finset V) := [');s=s.replace('}\n\ndef BP',']\n\ndef bases : Finset (Finset V) := baseList.toFinset\n\ndef BP');(p/'Bases.lean').write_text(s)
for k in range(8):
 out='import Bases\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace CommonBasis332371\n'
 for i in range(10*k,min(10*k+10,76)):
  A=f(o['bases'][i]);out+=f'''theorem check_{i} : baseList.all (fun b => decide (∀ e ∈ ({A} : Finset V) \\ b,
    ∃ f ∈ b \\ ({A} : Finset V), insert f (({A} : Finset V).erase e) ∈ bases)) = true := by decide
'''
 out+='end CommonBasis332371\n';(p/f'Cases{k}.lean').write_text(out)
s=(p/'Endpoint.lean').read_text();s=s.replace('simp only [bases, Finset.mem_insert, Finset.mem_singleton] at ha','simp only [bases, List.mem_toFinset, baseList, List.mem_cons, List.mem_singleton] at ha')
for i in range(76):s=s.replace(f'  · simpa only [Finset.all_eq_true, Finset.any_eq_true, decide_eq_true_eq] using check_{i}',f'  · intro b hb\n    exact (List.all_eq_true.mp check_{i}) b (by simpa [bases] using hb) |>.of_decide_eq_true')
# use ordinary of_decide_eq_true on the resulting Bool equality
s=s.replace('exact (List.all_eq_true.mp','exact of_decide_eq_true ((List.all_eq_true.mp').replace(') |>.of_decide_eq_true', '))')
(p/'Endpoint.lean').write_text(s)
