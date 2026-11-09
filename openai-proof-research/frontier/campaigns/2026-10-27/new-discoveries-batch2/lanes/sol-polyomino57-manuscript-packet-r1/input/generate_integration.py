from generate_cases import *
rr=json.loads((L/'frozen/frozen/inputs/compression/verification.json').read_text())['receipts'];rr=[r for r in rr if r['verified']=='potential-inequalities' and (r['a'],r['b'],r['e'])!=(10,10,1)]
done=set((L/'completed-modules.txt').read_text().splitlines())|{'C10_8_1Case'}
triples=[];names=[];imports=['Completed','F740Case','F830Case','F840Case']
for r in rr:
 a,b,e=(r[t] for t in ['a','b','e']);triples.append((a,b,e));ns=('C' if f'C{a}_{b}_{e}Case' in done else 'R')+f'{a}_{b}_{e}';imports.append(ns+'Case');names.append(ns+f'.case_{a}_{b}_{e}')
for a,b,e in [(7,4,0),(8,3,0),(8,4,0)]:triples.append((a,b,e));names.append(f'F{a}{b}{e}.case_{a}_{b}_{e}')
s=''.join('import '+m+'\n' for m in imports)+'''set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.AllCases
open Polyomino57
'''
s+='def residual : Finset (ℤ × ℤ × ℤ) := {'+','.join(f'({a},{b},{e})' for a,b,e in triples)+'}\n'
s+='theorem residual_eq : canonicalCases \\ completed = residual := by decide\n'
s+='''theorem remaining : RemainingCases := by
  intro c hc hn
  have hm : c ∈ residual := by
    rw [← residual_eq]
    exact Finset.mem_sdiff.mpr ⟨hc,hn⟩
  simp only [residual, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with '''+' | '.join('rfl' for _ in triples)+'\n'+''.join('  · exact '+n+'\n' for n in names)
s+='''theorem finiteCases : FiniteCases := finiteCases_iff_remaining.mpr remaining
 theorem universalContainer : UniversalContainer 11 witness := universalContainer_of_remaining remaining
 theorem eligible : EligibleSize 11 57 := ⟨witness,witness_card,universalContainer⟩
 theorem minimum_le : minimumSize 11 ≤ 57 := by
  classical
  have hx : ∃ m, EligibleSize 11 m := ⟨57,eligible⟩
  unfold minimumSize
  rw [dite_eq_left hx]
  exact Nat.find_min' hx eligible
 theorem source_refutation : ¬ SourceFormula := by
  intro h
  have he := h 11 (by decide)
  have hl := minimum_le
  change minimumSize 11 = 58 at he
  omega
end Polyomino57.Diagonal.FiniteProof.AllCases
'''
for d in ['formal','dev']:(L/d/'AllCases.lean').write_text(s)
