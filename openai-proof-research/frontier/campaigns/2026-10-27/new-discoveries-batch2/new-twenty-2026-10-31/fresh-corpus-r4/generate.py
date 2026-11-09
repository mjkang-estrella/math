from pathlib import Path
from itertools import product
from math import isqrt
import json
p=Path(__file__).parent
A=[1,2,4,8,16]; B=[0,2,3,5,7]
def raw(t):
 a,b,c,d=t;return (a+d,(a-d)**2+4*b*c)
def key(t):
 s,D=raw(t);r=isqrt(D);return (s+r,0) if r*r==D else (s,D)
def inc(p,q):
 s,D=p;t,E=q
 return D!=E if s==t else (D-E-(t-s)**2)**2!=4*(t-s)**2*E
reps={}
for t in product(B,repeat=4):reps.setdefault(key(t),t)
assert len(reps)==118
assert all(inc(x,y) for x,y in product(reps,repeat=2) if x!=y)
assert len({key(t) for t in product(A,repeat=4)})==115
(p/'diagnostic.json').write_text(json.dumps({'A':A,'B_with_zero':B,'A_count':115,'B_count':118,'representatives':[{'key':k,'entries':v} for k,v in sorted(reps.items())]},indent=2))
f=p/'lean/Spectral.lean';s=f.read_text().split('\ndef tuples')[0].split('end SpectralExclusion')[0]
s+='''
def tuples (A : Finset ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := A ×ˢ A ×ˢ A ×ˢ A
def tupleKey (t : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ := canon (raw t.1 t.2.1 t.2.2.1 t.2.2.2)
noncomputable def omega (A : Finset ℕ) : Finset ℝ := by
  classical
  exact (tuples A).image (fun t => value (raw t.1 t.2.1 t.2.2.1 t.2.2.2))

theorem omega_eq (A : Finset ℕ) : omega A = ((tuples A).image tupleKey).image value := by
  classical
  simp only [omega, Finset.image_image]
  congr 1
  funext t
  exact (canon_sound _).symm

def positiveSet : Finset ℕ := {1,2,4,8,16}
def zeroSet : Finset ℕ := {0,2,3,5,7}
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem positive_keys : ((tuples positiveSet).image tupleKey).card = 115 := by decide +kernel

theorem zero_keys : ((tuples zeroSet).image tupleKey).card = 118 := by decide +kernel

theorem zero_separated : ∀ p ∈ (tuples zeroSet).image tupleKey,
    ∀ q ∈ (tuples zeroSet).image tupleKey, p ≠ q → incompatible p q := by decide +kernel

theorem positive_count_le : (omega positiveSet).card ≤ 115 := by
  rw [omega_eq]
  exact (Finset.card_image_le).trans_eq positive_keys

theorem zero_count : (omega zeroSet).card = 118 := by
  classical
  rw [omega_eq, Finset.card_image_iff.mpr, zero_keys]
  intro p hp q hq he
  by_contra hn
  exact incompatible_sound (zero_separated p hp q hq hn) he

#print axioms positive_count_le
#print axioms zero_count
end SpectralExclusion
'''
f.write_text(s)
