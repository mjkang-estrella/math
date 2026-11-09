from pathlib import Path
import ast,re,json
w=Path(__file__).resolve().parent
src=(w.parent/'coxeter-spectral-r2/AutomatonCertificate.lean').read_text()
out=['import WordCounting','import SpectralDefinitions','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option linter.unusedSimpArgs false','namespace ConcreteMachine330264','open RACGNormal330264 RACGSemantics330264','abbrev S := Fin 38','abbrev A := Fin 19']
totals={}
for name in ['G','H']:
 es=ast.literal_eval(re.search(r'def edges'+name+r' :.*? := (\[.*?\])',src).group(1))
 states=[[]]+[[a] for a in range(19)]+[sorted(e) for e in es]
 adj=lambda a,b:(a,b) in es or (b,a) in es
 rows=[]
 for s in states:
  rows.append([38 if a in s else states.index(sorted([a]+[b for b in s if adj(a,b)])) for a in range(19)])
 out += [f'def states{name} : List (List Nat) := {states}',f'def rows{name} : List (List Nat) := {rows}',f'def state{name} (s : S) : Finset A := ((states{name}[s.val]!).map (fun a => (⟨a % 19, Nat.mod_lt _ (by decide)⟩ : A))).toFinset',f'def next{name} (s : S) (a : A) : Option S :=\n  let n := (rows{name}[s.val]!)[a.val]!\n  if h : n < 38 then some ⟨n, h⟩ else none',f'def machine{name} : Machine ActualSpectra330264.{name} S where',f'  state := state{name}',f'  next := next{name}','  initial := 0','  initial_empty := by decide +kernel','  next_spec := by decide +kernel']
 vals=[1]*38
 out += [f'def v{name}0 (s : S) : Nat := ({vals} : List Nat)[s.val]!',f'theorem stage{name}0 (s : S) : machine{name}.wordCount 0 s = v{name}0 s := by\n  rw [Machine.wordCount_zero]\n  have h : ∀ s : S, v{name}0 s = 1 := by decide +kernel\n  exact (h s).symm']
 for k in range(1,19):
  vals=[sum(vals[t] for t in row if t!=38) for row in rows]
  out += [f'def v{name}{k} (s : S) : Nat := ({vals} : List Nat)[s.val]!',f'theorem calc{name}{k} : ∀ s : S, (∑ a : A, (next{name} s a).elim 0 (fun t => v{name}{k-1} t)) = v{name}{k} s := by decide +kernel',f'theorem stage{name}{k} (s : S) : machine{name}.wordCount {k} s = v{name}{k} s := by\n  rw [Machine.wordCount_succ]\n  simp_rw [stage{name}{k-1}]\n  exact calc{name}{k} s']
 totals[name]=vals[0]
 out += [f'theorem growth{name} : geodesicGrowth ActualSpectra330264.{name} 18 = {vals[0]} := by\n  rw [Machine.geodesicGrowth_eq (M := machine{name})]\n  exact stage{name}18 0',f'#print axioms growth{name}']
out+=['theorem actual_growth_differ : geodesicGrowth ActualSpectra330264.G 18 ≠ geodesicGrowth ActualSpectra330264.H 18 := by\n  rw [growthG, growthH]\n  decide +kernel','#print axioms actual_growth_differ','end ConcreteMachine330264']
(w/'ConcreteMachine.lean').write_text('\n'.join(out)+'\n')
(w/'new-counts.json').write_text(json.dumps(totals,indent=2))
print(totals)
