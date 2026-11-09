import AntimagicModel
namespace Antimagic
open Finset

def internalEdges (t n : ℕ) : ℕ := ∑ h ∈ range n, if 1 ≤ h then t ^ h else 0

def offset (t n h : ℕ) : ℕ := ∑ g ∈ range n, if h < g then t ^ g else 0

def center (t n : ℕ) : ℕ := (internalEdges t n - t) / 2 + 1

def patchedIndex (t h i : ℕ) : ℕ :=
  if t = 2 ∧ h = 2 ∧ (i = 1 ∨ i = 3) then 4 - i else i

def internalLabel (t n h i : ℕ) : ℕ :=
  let N := internalEdges t n
  let Z := center t n
  if h = 1 then if i = 0 then Z else N - t + 1 + i
  else
    let r := offset t n h + patchedIndex t h i
    let d := 1 + r / 2
    if r % 2 = 0 then Z - d else Z + d

def sigma (k a : ℕ) : ℕ := if a ≤ k then 2 * a else 2 * (a - k) - 1

def largeLabel (t n h i : ℕ) : ℕ :=
  if h < n then internalLabel t n h i else
    let N := internalEdges t n
    let q := t ^ (n - 1)
    let Z := center t n
    let pl := internalLabel t n (n - 1) (i / t)
    let a := if Z < pl then pl - Z else q + 1 + pl - Z
    let j := i % t
    let lam := fun b x => N + (b - 1) * q + x
    if j < t - 2 then
      let b := j / 2 + 1
      if j % 2 = 0 then lam b a else lam (t + 1 - b) (q + 1 - a)
    else if j = t - 2 then lam (t / 2) a
    else lam (t / 2 + 1) (q + 1 - sigma (q / 2) a)

/-- Depth two: source ingredients (published Lemmas 2.2 and 2.9). -/
def depthTwoLabel (t h i : ℕ) : ℕ :=
  let s := t / 2
  if h = 1 then if i = 0 then 2 else 3 * s + 2 - i else
    let p := i / t
    let j := i % t
    if p = 0 then
      if j = 0 then 1 else if j ≤ s then j + 2 else 2 * s + 1 + j
    else
      let a := p - 1
      let k := s - 1
      let q := t - 1
      let beta := 2 * t + (s - 1) * q
      if j < t - 2 then
        let b := j / 2
        if j % 2 = 0 then 2 * t + b * q + a + 1
        else 2 * t + (t - 1 - b) * q + (q - a)
      else if a ≤ k then
        if j = t - 2 then beta + 2 * a + 1 else beta + 3 * k + 2 - a
      else
        let r := a - k
        if j = t - 2 then beta + 2 * r else beta + 4 * k + 3 - r

/-- Natural labels (already shifted to 1..m). The binary depth-two case is
exactly published Figure 5. This is a total formula, not a proof of validity. -/
def label (t n h i : ℕ) : ℕ :=
  if n = 1 then i + 1
  else if n = 2 then
    if t = 2 then
      if h = 1 then if i = 0 then 1 else 4
      else if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 6 else 5
    else depthTwoLabel t h i
  else largeLabel t n h i

theorem patchedIndex_involutive (i : ℕ) :
    patchedIndex 2 2 (patchedIndex 2 2 i) = i := by
  by_cases h1 : i = 1
  · subst i; decide
  by_cases h3 : i = 3
  · subst i; decide
  simp [patchedIndex, h1, h3]

/-- The elementary shell identity underlying all internal children sums. -/
theorem shell_pair_sum (Z d : ℕ) (hd : d ≤ Z) : (Z - d) + (Z + d) = 2 * Z := by
  omega

theorem sigma_lower (k a : ℕ) (ha : a ≤ k) : sigma k a = 2 * a := by
  simp [sigma, ha]

/-- Algebraic properness reduction for adjacent unpatched internal rows. -/
theorem translated_ne (c a b : ℕ) (hab : a ≠ b) : a + c ≠ b + c := by omega

/-- Formula agreement at the source Figure 5. -/
theorem figureFive :
    (List.range 2).map (label 2 2 1) = [1, 4] ∧
    (List.range 4).map (label 2 2 2) = [2, 3, 6, 5] := by decide

end Antimagic
