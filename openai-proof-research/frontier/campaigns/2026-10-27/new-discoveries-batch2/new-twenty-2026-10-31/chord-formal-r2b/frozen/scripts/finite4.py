from pathlib import Path
words=['11234234','12134234','12314234','12341234']
out=['import ChordSanity','namespace Chord','set_option maxRecDepth 10000','set_option maxHeartbeats 6000000']
for k,w in enumerate(words):
    t=[next(j for j in range(8) if j!=i and w[j]==w[i]) for i in range(8)]
    out += [f'/-- Literal source/reviewer word {w}. -/',f'def exception{k} : Diagram 4 where',
            '  partner i := ⟨(['+','.join(map(str,t))+'].getD i.val 0) % 8, Nat.mod_lt _ (by decide)⟩',
            '  involutive := by decide','  noFixed := by decide',
            f'theorem exception{k}_values : ∀ c : Sides 4, boundary exception{k} c = 2 ∨ boundary exception{k} c = 4 := by decide',
            f'theorem exception{k}_one : ∃ c : Sides 4, HasGenus exception{k} c 1 := by decide',
            f'theorem exception{k}_two : ∃ c : Sides 4, HasGenus exception{k} c 2 := by decide',
            f'theorem exception{k}_range : Range12 exception{k} := by',
            '  intro g','  constructor','  · rintro ⟨c,h⟩',f'    have := exception{k}_values c',
            '    unfold HasGenus at h','    omega','  · rintro (rfl | rfl)',
            f'    · exact exception{k}_one',f'    · exact exception{k}_two']
out+=['end Chord']
Path('ChordFourWitnesses.lean').write_text('\n'.join(out)+'\n')
