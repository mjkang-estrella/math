import TraceFormal
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace TraceFormal
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def e1 {K : Type*} [CommRing K] (A _B _C : Mat K) : K :=
  tr (A * A)
def e2 {K : Type*} [CommRing K] (_A B _C : Mat K) : K :=
  tr (B * B)
def e3 {K : Type*} [CommRing K] (_A _B C : Mat K) : K :=
  tr (C * C)
def e4 {K : Type*} [CommRing K] (A B _C : Mat K) : K :=
  tr (A * B)
def e5 {K : Type*} [CommRing K] (A _B C : Mat K) : K :=
  tr (A * C)
def e6 {K : Type*} [CommRing K] (_A B C : Mat K) : K :=
  tr (B * C)
def e7 {K : Type*} [CommRing K] (A _B _C : Mat K) : K :=
  tr (A * A * A)
def e8 {K : Type*} [CommRing K] (_A B _C : Mat K) : K :=
  tr (B * B * B)
def e9 {K : Type*} [CommRing K] (_A _B C : Mat K) : K :=
  tr (C * C * C)
def e10 {K : Type*} [CommRing K] (A B _C : Mat K) : K :=
  tr (A * A * B)
def e11 {K : Type*} [CommRing K] (A _B C : Mat K) : K :=
  tr (A * A * C)
def e12 {K : Type*} [CommRing K] (A B _C : Mat K) : K :=
  tr (B * B * A)
def e13 {K : Type*} [CommRing K] (_A B C : Mat K) : K :=
  tr (B * B * C)
def e14 {K : Type*} [CommRing K] (A _B C : Mat K) : K :=
  tr (C * C * A)
def e15 {K : Type*} [CommRing K] (_A B C : Mat K) : K :=
  tr (C * C * B)
def e16 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * B * C) + tr (A * C * B)
def e17 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * B * C) - tr (A * C * B)
def e18 {K : Type*} [CommRing K] (A B _C : Mat K) : K :=
  tr (A * A * B * B) - tr (A * B * A * B)
def e19 {K : Type*} [CommRing K] (A _B C : Mat K) : K :=
  tr (A * A * C * C) - tr (A * C * A * C)
def e20 {K : Type*} [CommRing K] (_A B C : Mat K) : K :=
  tr (B * B * C * C) - tr (B * C * B * C)
def e21 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * B * C) + tr (A * A * C * B) - 2 * tr (A * B * A * C)
def e22 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * B * A * C) + tr (B * B * C * A) - 2 * tr (B * A * B * C)
def e23 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (C * C * A * B) + tr (C * C * B * A) - 2 * tr (C * A * C * B)
def e24 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * B * C) - tr (A * A * C * B)
def e25 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * B * A * C) - tr (B * B * C * A)
def e26 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (C * C * A * B) - tr (C * C * B * A)
def e27 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * B * A * C) - tr (A * A * C * A * B)
def e28 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * B * A * B * C) - tr (B * B * C * B * A)
def e29 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (C * C * B * C * A) - tr (C * C * A * C * B)
def e30 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * A * B * A * C) + tr (A * A * B * B * C) - tr (A * B * C * A * B) - tr (A * A * C * B * B)
def e31 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (C * A * C * A * B) + tr (A * A * C * C * B) - tr (A * C * B * A * C) - tr (A * A * B * C * C)
def e32 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * C * B * C * A) + tr (C * C * B * B * A) - tr (B * C * A * B * C) - tr (C * C * A * B * B)
def e33 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * B * B * C) + tr (A * A * C * B * B) + tr (A * B * A * B * C) + tr (A * B * A * C * B) - 2 * tr (A * A * B * C * B) - 2 * tr (A * B * B * A * C)
def e34 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * C * C * B) + tr (A * A * B * C * C) + tr (A * C * A * C * B) + tr (A * C * A * B * C) - 2 * tr (A * A * C * B * C) - 2 * tr (A * C * C * A * B)
def e35 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * B * C * C * A) + tr (B * B * A * C * C) + tr (B * C * B * C * A) + tr (B * C * B * A * C) - 2 * tr (B * B * C * A * C) - 2 * tr (B * C * C * B * A)
def relation6 {K : Type*} [CommRing K] (t : ℕ → K) : K :=
  t 1 * t 35 + t 4 * t 34 + t 5 * t 33 - 2 * t 7 * t 20 +
  2 * t 10 * t 23 + 2 * t 11 * t 22 - 2 * t 12 * t 19 -
  2 * t 14 * t 18 + t 16 * t 21 - 3 * t 17 * t 24

def actualE {K : Type*} [CommRing K] (A B C : Mat K) (i : ℕ) : K :=
  match i with
  | 1 => e1 A B C
  | 2 => e2 A B C
  | 3 => e3 A B C
  | 4 => e4 A B C
  | 5 => e5 A B C
  | 6 => e6 A B C
  | 7 => e7 A B C
  | 8 => e8 A B C
  | 9 => e9 A B C
  | 10 => e10 A B C
  | 11 => e11 A B C
  | 12 => e12 A B C
  | 13 => e13 A B C
  | 14 => e14 A B C
  | 15 => e15 A B C
  | 16 => e16 A B C
  | 17 => e17 A B C
  | 18 => e18 A B C
  | 19 => e19 A B C
  | 20 => e20 A B C
  | 21 => e21 A B C
  | 22 => e22 A B C
  | 23 => e23 A B C
  | 24 => e24 A B C
  | 25 => e25 A B C
  | 26 => e26 A B C
  | 27 => e27 A B C
  | 28 => e28 A B C
  | 29 => e29 A B C
  | 30 => e30 A B C
  | 31 => e31 A B C
  | 32 => e32 A B C
  | 33 => e33 A B C
  | 34 => e34 A B C
  | 35 => e35 A B C
  | _ => 0
private theorem cyc0 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (A * (B * A))) = tr (A * (A * (A * B))) := by
  calc
    _ = tr ((A * (A * B)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (A * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc1 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (A * (B * (B * A)))) = tr (A * (A * (A * (B * B)))) := by
  calc
    _ = tr ((A * (A * (B * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (A * (B * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc2 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (A * (B * (B * (C * (C * A)))))) = tr (A * (A * (A * (B * (B * (C * C)))))) := by
  calc
    _ = tr ((A * (A * (B * (B * (C * C))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (A * (B * (B * (C * C)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc3 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (A * (B * (C * A)))) = tr (A * (A * (A * (B * C)))) := by
  calc
    _ = tr ((A * (A * (B * C))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (A * (B * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc4 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (A * (B * (C * (C * (B * A)))))) = tr (A * (A * (A * (B * (C * (C * B)))))) := by
  calc
    _ = tr ((A * (A * (B * (C * (C * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (A * (B * (C * (C * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc5 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (A * (C * A))) = tr (A * (A * (A * C))) := by
  calc
    _ = tr ((A * (A * C)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (A * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc6 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (A * (C * (C * (B * (B * A)))))) = tr (A * (A * (A * (C * (C * (B * B)))))) := by
  calc
    _ = tr ((A * (A * (C * (C * (B * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (A * (C * (C * (B * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc7 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * A)) = tr (A * (A * B)) := by
  calc
    _ = tr ((A * B) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc8 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * A))) = tr (A * (A * (A * B))) := by
  calc
    _ = tr ((A * B) * (A * A)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * A) * (A * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc9 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * (A * B)))) = tr (A * (A * (B * (A * B)))) := by
  calc
    _ = tr ((A * B) * (A * (A * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (A * B)) * (A * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc10 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * (B * A)))) = tr (A * (A * (B * (A * B)))) := by
  calc
    _ = tr ((A * (B * (A * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (A * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc11 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * (B * (C * A))))) = tr (A * (A * (B * (A * (B * C))))) := by
  calc
    _ = tr ((A * (B * (A * (B * C)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (A * (B * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc12 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * (B * (C * (C * A)))))) = tr (A * (A * (B * (A * (B * (C * C)))))) := by
  calc
    _ = tr ((A * (B * (A * (B * (C * C))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (A * (B * (C * C)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc13 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * (C * (C * A))))) = tr (A * (A * (B * (A * (C * C))))) := by
  calc
    _ = tr ((A * (B * (A * (C * C)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (A * (C * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc14 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * (C * (C * (A * B)))))) = tr (A * (B * (A * (B * (A * (C * C)))))) := by
  calc
    _ = tr ((A * (B * (A * (C * C)))) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (B * (A * (C * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc15 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (A * (C * (C * (B * A)))))) = tr (A * (A * (B * (A * (C * (C * B)))))) := by
  calc
    _ = tr ((A * (B * (A * (C * (C * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (A * (C * (C * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc16 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * A))) = tr (A * (A * (B * B))) := by
  calc
    _ = tr ((A * (B * B)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc17 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * (A * A)))) = tr (A * (A * (A * (B * B)))) := by
  calc
    _ = tr ((A * (B * B)) * (A * A)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * A) * (A * (B * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc18 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * (A * (C * A))))) = tr (A * (A * (B * (B * (A * C))))) := by
  calc
    _ = tr ((A * (B * (B * (A * C)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (B * (A * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc19 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * (A * (C * (C * A)))))) = tr (A * (A * (B * (B * (A * (C * C)))))) := by
  calc
    _ = tr ((A * (B * (B * (A * (C * C))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (B * (A * (C * C)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc20 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * (C * A)))) = tr (A * (A * (B * (B * C)))) := by
  calc
    _ = tr ((A * (B * (B * C))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (B * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc21 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * (C * (A * (C * A)))))) = tr (A * (A * (B * (B * (C * (A * C)))))) := by
  calc
    _ = tr ((A * (B * (B * (C * (A * C))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (B * (C * (A * C)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc22 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * (C * (C * A))))) = tr (A * (A * (B * (B * (C * C))))) := by
  calc
    _ = tr ((A * (B * (B * (C * C)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (B * (C * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc23 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (B * (C * (C * (A * A)))))) = tr (A * (A * (A * (B * (B * (C * C)))))) := by
  calc
    _ = tr ((A * (B * (B * (C * C)))) * (A * A)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * A) * (A * (B * (B * (C * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc24 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * A))) = tr (A * (A * (B * C))) := by
  calc
    _ = tr ((A * (B * C)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc25 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (A * A)))) = tr (A * (A * (A * (B * C)))) := by
  calc
    _ = tr ((A * (B * C)) * (A * A)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * A) * (A * (B * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc26 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (A * B)))) = tr (A * (B * (A * (B * C)))) := by
  calc
    _ = tr ((A * (B * C)) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (B * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc27 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (A * (C * A))))) = tr (A * (A * (B * (C * (A * C))))) := by
  calc
    _ = tr ((A * (B * (C * (A * C)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (C * (A * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc28 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (A * (C * (A * B)))))) = tr (A * (B * (A * (B * (C * (A * C)))))) := by
  calc
    _ = tr ((A * (B * (C * (A * C)))) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (B * (C * (A * C))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc29 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (A * (C * (B * A)))))) = tr (A * (A * (B * (C * (A * (C * B)))))) := by
  calc
    _ = tr ((A * (B * (C * (A * (C * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (C * (A * (C * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc30 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (B * A)))) = tr (A * (A * (B * (C * B)))) := by
  calc
    _ = tr ((A * (B * (C * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (C * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc31 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (C * A)))) = tr (A * (A * (B * (C * C)))) := by
  calc
    _ = tr ((A * (B * (C * C))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (C * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc32 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (C * (A * (A * B)))))) = tr (A * (A * (B * (A * (B * (C * C)))))) := by
  calc
    _ = tr ((A * (B * (C * C))) * (A * (A * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (A * B)) * (A * (B * (C * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc33 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (C * (A * B))))) = tr (A * (B * (A * (B * (C * C))))) := by
  calc
    _ = tr ((A * (B * (C * C))) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (B * (C * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc34 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (C * (A * (B * A)))))) = tr (A * (A * (B * (C * (C * (A * B)))))) := by
  calc
    _ = tr ((A * (B * (C * (C * (A * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (C * (C * (A * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc35 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (C * (B * A))))) = tr (A * (A * (B * (C * (C * B))))) := by
  calc
    _ = tr ((A * (B * (C * (C * B)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (B * (C * (C * B))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc36 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (B * (C * (C * (B * (A * A)))))) = tr (A * (A * (A * (B * (C * (C * B)))))) := by
  calc
    _ = tr ((A * (B * (C * (C * B)))) * (A * A)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * A) * (A * (B * (C * (C * B))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc37 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * A)) = tr (A * (A * C)) := by
  calc
    _ = tr ((A * C) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc38 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * A))) = tr (A * (A * (A * C))) := by
  calc
    _ = tr ((A * C) * (A * A)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * A) * (A * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc39 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * B))) = tr (A * (B * (A * C))) := by
  calc
    _ = tr ((A * C) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc40 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (B * (A * (B * C)))))) = tr (A * (B * (A * (B * (C * (A * C)))))) := by
  calc
    _ = tr ((A * C) * (A * (B * (A * (B * C))))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * (A * (B * C)))) * (A * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc41 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (B * B)))) = tr (A * (B * (B * (A * C)))) := by
  calc
    _ = tr ((A * C) * (A * (B * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * B)) * (A * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc42 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (B * (B * (A * C)))))) = tr (A * (B * (B * (A * (C * (A * C)))))) := by
  calc
    _ = tr ((A * C) * (A * (B * (B * (A * C))))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * (B * (A * C)))) * (A * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc43 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (B * C)))) = tr (A * (B * (C * (A * C)))) := by
  calc
    _ = tr ((A * C) * (A * (B * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * C)) * (A * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc44 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (C * (A * B))))) = tr (A * (B * (A * (C * (A * C))))) := by
  calc
    _ = tr ((A * (C * (A * C))) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (C * (A * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc45 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (C * (A * (B * B)))))) = tr (A * (B * (B * (A * (C * (A * C)))))) := by
  calc
    _ = tr ((A * (C * (A * C))) * (A * (B * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * B)) * (A * (C * (A * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc46 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (C * (B * A))))) = tr (A * (A * (C * (A * (C * B))))) := by
  calc
    _ = tr ((A * (C * (A * (C * B)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (A * (C * B))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc47 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (C * (B * (A * B)))))) = tr (A * (B * (A * (C * (A * (C * B)))))) := by
  calc
    _ = tr ((A * (C * (A * (C * B)))) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (C * (A * (C * B))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc48 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (A * (C * (B * (B * A)))))) = tr (A * (A * (C * (A * (C * (B * B)))))) := by
  calc
    _ = tr ((A * (C * (A * (C * (B * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (A * (C * (B * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc49 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * A))) = tr (A * (A * (C * B))) := by
  calc
    _ = tr ((A * (C * B)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc50 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (A * (A * (B * C)))))) = tr (A * (A * (B * (C * (A * (C * B)))))) := by
  calc
    _ = tr ((A * (C * B)) * (A * (A * (B * C)))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (A * (B * C))) * (A * (C * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc51 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (A * B)))) = tr (A * (B * (A * (C * B)))) := by
  calc
    _ = tr ((A * (C * B)) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (C * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc52 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (A * (B * C))))) = tr (A * (B * (C * (A * (C * B))))) := by
  calc
    _ = tr ((A * (C * B)) * (A * (B * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * C)) * (A * (C * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc53 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (A * (B * (C * A)))))) = tr (A * (A * (C * (B * (A * (B * C)))))) := by
  calc
    _ = tr ((A * (C * (B * (A * (B * C))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (B * (A * (B * C)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc54 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (A * C)))) = tr (A * (C * (A * (C * B)))) := by
  calc
    _ = tr ((A * (C * B)) * (A * C)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * C) * (A * (C * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc55 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (B * A)))) = tr (A * (A * (C * (B * B)))) := by
  calc
    _ = tr ((A * (C * (B * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (B * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc56 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (B * (A * (A * C)))))) = tr (A * (A * (C * (A * (C * (B * B)))))) := by
  calc
    _ = tr ((A * (C * (B * B))) * (A * (A * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (A * C)) * (A * (C * (B * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc57 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (B * (A * C))))) = tr (A * (C * (A * (C * (B * B))))) := by
  calc
    _ = tr ((A * (C * (B * B))) * (A * C)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * C) * (A * (C * (B * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc58 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (B * (A * (C * A)))))) = tr (A * (A * (C * (B * (B * (A * C)))))) := by
  calc
    _ = tr ((A * (C * (B * (B * (A * C))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (B * (B * (A * C)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc59 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (B * (C * A)))) = tr (A * (A * (C * (B * C)))) := by
  calc
    _ = tr ((A * (C * (B * C))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (B * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc60 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * A))) = tr (A * (A * (C * C))) := by
  calc
    _ = tr ((A * (C * C)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc61 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (A * (A * (B * B)))))) = tr (A * (A * (B * (B * (A * (C * C)))))) := by
  calc
    _ = tr ((A * (C * C)) * (A * (A * (B * B)))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (A * (B * B))) * (A * (C * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc62 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (A * B)))) = tr (A * (B * (A * (C * C)))) := by
  calc
    _ = tr ((A * (C * C)) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (C * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc63 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (A * (B * A))))) = tr (A * (A * (C * (C * (A * B))))) := by
  calc
    _ = tr ((A * (C * (C * (A * B)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (C * (A * B))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc64 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (A * (B * (A * B)))))) = tr (A * (B * (A * (B * (A * (C * C)))))) := by
  calc
    _ = tr ((A * (C * C)) * (A * (B * (A * B)))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * (A * B))) * (A * (C * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc65 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (A * (B * B))))) = tr (A * (B * (B * (A * (C * C))))) := by
  calc
    _ = tr ((A * (C * C)) * (A * (B * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * B)) * (A * (C * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc66 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (A * (B * (B * A)))))) = tr (A * (A * (C * (C * (A * (B * B)))))) := by
  calc
    _ = tr ((A * (C * (C * (A * (B * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (C * (A * (B * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc67 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (B * A)))) = tr (A * (A * (C * (C * B)))) := by
  calc
    _ = tr ((A * (C * (C * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (C * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc68 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (B * (A * (A * B)))))) = tr (A * (A * (B * (A * (C * (C * B)))))) := by
  calc
    _ = tr ((A * (C * (C * B))) * (A * (A * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (A * B)) * (A * (C * (C * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc69 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (B * (A * B))))) = tr (A * (B * (A * (C * (C * B))))) := by
  calc
    _ = tr ((A * (C * (C * B))) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (A * (C * (C * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc70 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (B * (A * (B * A)))))) = tr (A * (A * (C * (C * (B * (A * B)))))) := by
  calc
    _ = tr ((A * (C * (C * (B * (A * B))))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (C * (B * (A * B)))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc71 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (B * (B * A))))) = tr (A * (A * (C * (C * (B * B))))) := by
  calc
    _ = tr ((A * (C * (C * (B * B)))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (A * (C * (C * (B * B))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc72 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (A * (C * (C * (B * (B * (A * A)))))) = tr (A * (A * (A * (C * (C * (B * B)))))) := by
  calc
    _ = tr ((A * (C * (C * (B * B)))) * (A * A)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * A) * (A * (C * (C * (B * B))))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc73 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (A * B)) = tr (A * (B * B)) := by
  calc
    _ = tr (B * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * B) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc74 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (A * (B * C))) = tr (A * (B * (C * B))) := by
  calc
    _ = tr (B * (A * (B * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * C)) * B) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc75 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (A * (B * (C * C)))) = tr (A * (B * (C * (C * B)))) := by
  calc
    _ = tr (B * (A * (B * (C * C)))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * (C * C))) * B) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc76 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (A * (C * C))) = tr (A * (C * (C * B))) := by
  calc
    _ = tr (B * (A * (C * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (C * C)) * B) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc77 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * (A * C))) = tr (A * (C * (B * B))) := by
  calc
    _ = tr ((B * B) * (A * C)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * C) * (B * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc78 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * (A * (C * C)))) = tr (A * (C * (C * (B * B)))) := by
  calc
    _ = tr ((B * B) * (A * (C * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (C * C)) * (B * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc79 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * (C * (A * C)))) = tr (A * (C * (B * (B * C)))) := by
  calc
    _ = tr ((B * (B * C)) * (A * C)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * C) * (B * (B * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc80 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (A * C))) = tr (A * (C * (B * C))) := by
  calc
    _ = tr ((B * C) * (A * C)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * C) * (B * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc81 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (A * (C * B)))) = tr (A * (C * (B * (B * C)))) := by
  calc
    _ = tr ((B * C) * (A * (C * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (C * B)) * (B * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc82 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * B)) = tr (B * (B * C)) := by
  calc
    _ = tr ((B * C) * B) := by simp only [Matrix.mul_assoc]
    _ = tr (B * (B * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc83 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (C * (A * B)))) = tr (A * (B * (B * (C * C)))) := by
  calc
    _ = tr ((B * (C * C)) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (B * (C * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc84 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (C * B))) = tr (B * (B * (C * C))) := by
  calc
    _ = tr ((B * (C * C)) * B) := by simp only [Matrix.mul_assoc]
    _ = tr (B * (B * (C * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc85 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (A * C)) = tr (A * (C * C)) := by
  calc
    _ = tr (C * (A * C)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * C) * C) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc86 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (A * (C * B))) = tr (A * (C * (B * C))) := by
  calc
    _ = tr (C * (A * (C * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (C * B)) * C) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc87 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * B) = tr (B * C) := by
  calc
    _ = tr (C * B) := by simp only [Matrix.mul_assoc]
    _ = tr (B * C) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc88 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (B * B)) = tr (B * (B * C)) := by
  calc
    _ = tr (C * (B * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((B * B) * C) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc89 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * (A * B))) = tr (A * (B * (C * C))) := by
  calc
    _ = tr ((C * C) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (C * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc90 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * B)) = tr (B * (C * C)) := by
  calc
    _ = tr ((C * C) * B) := by simp only [Matrix.mul_assoc]
    _ = tr (B * (C * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc91 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * (B * B))) = tr (B * (B * (C * C))) := by
  calc
    _ = tr ((C * C) * (B * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((B * B) * (C * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc92 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (A * (B * (A * C)))) = tr (A * (B * (A * (C * B)))) := by
  calc
    _ = tr (B * (A * (B * (A * C)))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * (A * C))) * B) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc93 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * A)) = tr (A * (B * B)) := by
  calc
    _ = tr ((B * B) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (B * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc94 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * (A * (B * C)))) = tr (A * (B * (C * (B * B)))) := by
  calc
    _ = tr ((B * B) * (A * (B * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * C)) * (B * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc95 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * (C * A))) = tr (A * (B * (B * C))) := by
  calc
    _ = tr ((B * (B * C)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (B * (B * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc96 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * (C * (B * A)))) = tr (A * (B * (B * (C * B)))) := by
  calc
    _ = tr ((B * (B * (C * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (B * (B * (C * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc97 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (B * (C * (C * A)))) = tr (A * (B * (B * (C * C)))) := by
  calc
    _ = tr ((B * (B * (C * C))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (B * (B * (C * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc98 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (A * (B * C)))) = tr (A * (B * (C * (B * C)))) := by
  calc
    _ = tr ((B * C) * (A * (B * C))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * C)) * (B * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc99 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (B * (A * C)))) = tr (A * (C * (B * (C * B)))) := by
  calc
    _ = tr ((B * (C * B)) * (A * C)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * C) * (B * (C * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc100 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (B * (C * A)))) = tr (A * (B * (C * (B * C)))) := by
  calc
    _ = tr ((B * (C * (B * C))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (B * (C * (B * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc101 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (B * (C * (C * (B * A)))) = tr (A * (B * (C * (C * B)))) := by
  calc
    _ = tr ((B * (C * (C * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (B * (C * (C * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc102 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (A * (C * (A * B)))) = tr (A * (B * (C * (A * C)))) := by
  calc
    _ = tr ((C * (A * C)) * (A * B)) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * B) * (C * (A * C))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc103 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * A)) = tr (A * (C * C)) := by
  calc
    _ = tr ((C * C) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (C * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc104 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * (A * (B * B)))) = tr (A * (B * (B * (C * C)))) := by
  calc
    _ = tr ((C * C) * (A * (B * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (B * B)) * (C * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc105 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * (A * (C * B)))) = tr (A * (C * (B * (C * C)))) := by
  calc
    _ = tr ((C * C) * (A * (C * B))) := by simp only [Matrix.mul_assoc]
    _ = tr ((A * (C * B)) * (C * C)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc106 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * (B * A))) = tr (A * (C * (C * B))) := by
  calc
    _ = tr ((C * (C * B)) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (C * (C * B))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc107 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * (B * (B * A)))) = tr (A * (C * (C * (B * B)))) := by
  calc
    _ = tr ((C * (C * (B * B))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (C * (C * (B * B)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
private theorem cyc108 {K : Type*} [CommRing K] (A B C : Mat K) :
    tr (C * (C * (B * (C * A)))) = tr (A * (C * (C * (B * C)))) := by
  calc
    _ = tr ((C * (C * (B * C))) * A) := by simp only [Matrix.mul_assoc]
    _ = tr (A * (C * (C * (B * C)))) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]
theorem relation6_matrix {K : Type*} [Field K] [CharZero K] (A B C : Mat K)
    (ha : tr A = 0) (hb : tr B = 0) (hc : tr C = 0) :
    relation6 (actualE A B C) = 0 := by
  have h0 := fundamental_matrix A (A * B) B (C * (A * C))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h0
  have h1 := fundamental_matrix A A B (B * (C * (A * C)))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h1
  have h2 := fundamental_matrix A A (B * (A * (B * C))) C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h2
  have h3 := fundamental_matrix A A (A * B) (B * (C * C))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h3
  have h4 := fundamental_matrix A A A (B * (B * (C * C)))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h4
  have h5 := fundamental_matrix A A B (C * (C * (A * B)))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h5
  have h6 := fundamental_matrix A A (A * (B * C)) (C * B)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h6
  have h7 := fundamental_matrix A A A (B * (C * (C * B)))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h7
  have h8 := fundamental_matrix A A B (B * (A * (C * C)))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h8
  have h9 := fundamental_matrix A A (A * (B * B)) (C * C)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h9
  have h10 := fundamental_matrix A A (A * C) (C * (B * B))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h10
  have h11 := fundamental_matrix A A A (C * (C * (B * B)))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h11
  have h12 := fundamental_matrix A A (B * (A * B)) (C * C)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h12
  have h13 := fundamental_matrix A A (A * B) (C * (C * B))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h13
  have h14 := fundamental_matrix A A (B * (B * (A * C))) C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h14
  have h15 := fundamental_matrix A A B (C * (A * (C * B)))
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h15
  have h16 := fundamental_matrix A A C C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h16
  have h17 := fundamental_matrix A (B * B) C C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h17
  have h18 := fundamental_matrix A B B (C * C)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h18
  have h19 := fundamental_matrix A A B B
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h19
  have h20 := fundamental_matrix A B C (C * B)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h20
  have h21 := fundamental_matrix A B (B * C) C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h21
  have h22 := fundamental_matrix B B C C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h22
  have h23 := fundamental_matrix A A A (B * C)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h23
  have h24 := fundamental_matrix A A A B
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h24
  have h25 := fundamental_matrix A A A (B * B)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h25
  have h26 := fundamental_matrix A A A C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h26
  have h27 := fundamental_matrix A A (B * B) C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h27
  have h28 := fundamental_matrix A A (B * C) C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h28
  have h29 := fundamental_matrix A B C C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h29
  have h30 := fundamental_matrix A A (A * B) B
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h30
  have h31 := fundamental_matrix A A B (C * B)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h31
  have h32 := fundamental_matrix A A B C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h32
  have h33 := fundamental_matrix A A C (C * B)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h33
  have h34 := fundamental_matrix A B B C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h34
  have h35 := fundamental_matrix A A B C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h35
  have h36 := fundamental_matrix A A B (C * C)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h36
  have h37 := fundamental_matrix A (A * B) C C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h37
  have h38 := fundamental_matrix A (A * B) B C
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h38
  have h39 := fundamental_matrix A A B (B * C)
  simp only [fundamental, Matrix.mul_assoc, (cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), ha, hb, hc] at h39
  simp only [relation6, actualE, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, Matrix.mul_assoc]
  simp only [(cyc0 A B C), (cyc1 A B C), (cyc2 A B C), (cyc3 A B C), (cyc4 A B C), (cyc5 A B C), (cyc6 A B C), (cyc7 A B C), (cyc8 A B C), (cyc9 A B C), (cyc10 A B C), (cyc11 A B C), (cyc12 A B C), (cyc13 A B C), (cyc14 A B C), (cyc15 A B C), (cyc16 A B C), (cyc17 A B C), (cyc18 A B C), (cyc19 A B C), (cyc20 A B C), (cyc21 A B C), (cyc22 A B C), (cyc23 A B C), (cyc24 A B C), (cyc25 A B C), (cyc26 A B C), (cyc27 A B C), (cyc28 A B C), (cyc29 A B C), (cyc30 A B C), (cyc31 A B C), (cyc32 A B C), (cyc33 A B C), (cyc34 A B C), (cyc35 A B C), (cyc36 A B C), (cyc37 A B C), (cyc38 A B C), (cyc39 A B C), (cyc40 A B C), (cyc41 A B C), (cyc42 A B C), (cyc43 A B C), (cyc44 A B C), (cyc45 A B C), (cyc46 A B C), (cyc47 A B C), (cyc48 A B C), (cyc49 A B C), (cyc50 A B C), (cyc51 A B C), (cyc52 A B C), (cyc53 A B C), (cyc54 A B C), (cyc55 A B C), (cyc56 A B C), (cyc57 A B C), (cyc58 A B C), (cyc59 A B C), (cyc60 A B C), (cyc61 A B C), (cyc62 A B C), (cyc63 A B C), (cyc64 A B C), (cyc65 A B C), (cyc66 A B C), (cyc67 A B C), (cyc68 A B C), (cyc69 A B C), (cyc70 A B C), (cyc71 A B C), (cyc72 A B C), (cyc73 A B C), (cyc74 A B C), (cyc75 A B C), (cyc76 A B C), (cyc77 A B C), (cyc78 A B C), (cyc79 A B C), (cyc80 A B C), (cyc81 A B C), (cyc82 A B C), (cyc83 A B C), (cyc84 A B C), (cyc85 A B C), (cyc86 A B C), (cyc87 A B C), (cyc88 A B C), (cyc89 A B C), (cyc90 A B C), (cyc91 A B C), (cyc92 A B C), (cyc93 A B C), (cyc94 A B C), (cyc95 A B C), (cyc96 A B C), (cyc97 A B C), (cyc98 A B C), (cyc99 A B C), (cyc100 A B C), (cyc101 A B C), (cyc102 A B C), (cyc103 A B C), (cyc104 A B C), (cyc105 A B C), (cyc106 A B C), (cyc107 A B C), (cyc108 A B C)]
  linear_combination (6 / 1 : K) * h0 + (-3 / 1 : K) * h1 + (-3 / 1 : K) * h2 + (2 / 1 : K) * h3 + (-4 / 3 : K) * h4 + (-2 / 1 : K) * h5 + (3 / 1 : K) * h6 + (-2 / 3 : K) * h7 + (1 / 1 : K) * h8 + (2 / 1 : K) * h9 + (3 / 1 : K) * h10 + (-1 / 1 : K) * h11 + (1 / 1 : K) * h12 + (-1 / 1 : K) * h13 + (-3 / 1 : K) * h14 + (-3 / 1 : K) * h15 + (2 / 1 : K) * tr (A * (B * B)) * h16 + (-5 / 3 : K) * tr (A * A) * h17 + (1 / 3 : K) * tr (A * A) * h18 + (3 / 1 : K) * tr (A * (C * C)) * h19 + (-1 / 3 : K) * tr (A * A) * h20 + (-1 / 3 : K) * tr (A * A) * h21 + (-1 / 1 : K) * tr (A * (A * A)) * h22 + (1 / 1 : K) * tr (B * C) * h23 + (1 / 3 : K) * tr (B * (C * C)) * h24 + (1 / 2 : K) * tr (C * C) * h25 + (1 / 1 : K) * tr (B * (B * C)) * h26 + (1 / 2 : K) * tr (A * C) * h27 + (3 / 2 : K) * tr (A * B) * h28 + (-1 / 1 : K) * tr (A * (A * B)) * h29 + (1 / 2 : K) * tr (C * C) * h30 + (2 / 1 : K) * tr (A * C) * h31 + (1 / 1 : K) * tr (A * (C * B)) * h32 + (-1 / 2 : K) * tr (A * B) * h33 + (-1 / 1 : K) * tr (A * (A * C)) * h34 + (1 / 1 : K) * tr (A * (B * C)) * h35 + (-1 / 1 : K) * tr (A * B) * h36 + (1 / 1 : K) * tr (A * B) * h37 + (-5 / 1 : K) * tr (A * C) * h38 + (3 / 2 : K) * tr (A * C) * h39
#print axioms relation6_matrix
end TraceFormal
