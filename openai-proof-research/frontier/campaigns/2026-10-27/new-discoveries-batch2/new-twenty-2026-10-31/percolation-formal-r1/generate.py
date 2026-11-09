from pathlib import Path
import json
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r1')
data=json.loads((root.parent/'expanded-corpus-r164/outputs/percolation.json').read_text())[1]
lines=data['lines']
s='''import Definitions
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
def lineMasks : List Nat := '''+str(lines)+'''
def incidence (p l : Points 5) : Bool := (lineMasks[l.val]!).testBit p.val
def vx (p : Points 5) : Nat := if p.val < 25 then 1 else 0
def vy (p : Points 5) : Nat := if p.val < 25 then p.val / 5 else if p.val < 30 then 1 else 0
def vz (p : Points 5) : Nat := if p.val < 25 then p.val % 5 else if p.val < 30 then p.val-25 else 1
def dotZero (p l : Points 5) : Bool :=
  decide ((vx p * vx l + vy p * vy l + vz p * vz l) % 5 = 0)
theorem incidence_dot : ∀ p l, incidence p l = dotZero p l := by decide
'''
for field,statement in [
('line_degree','∀ l, card (List.finRange (size 5)) (fun p => incidence p l) = 6'),
('point_degree','∀ p, card (List.finRange (size 5)) (fun l => incidence p l) = 6'),
('join',"∀ p p', p ≠ p' → card (List.finRange (size 5)) (fun l => incidence p l && incidence p' l) = 1"),
('meet',"∀ l l', l ≠ l' → card (List.finRange (size 5)) (fun p => incidence p l && incidence p l') = 1")]:
 s+=f'theorem pg_{field} : {statement} := by decide\n'
s+='''def PG5 : Plane 5 where
  nontrivial := by decide
  inc := incidence
  line_degree := pg_line_degree
  point_degree := pg_point_degree
  join := pg_join
  meet := pg_meet
-- An explicit quadrangle also verifies nondegeneracy without relying on counting arguments.
theorem quadrangle : ∀ l : Points 5,
    card ([0,25,30,6] : List (Points 5)) (fun p => incidence p l) ≤ 2 := by decide
end Percolation
'''
(root/'src/Plane5.lean').write_text(s)
