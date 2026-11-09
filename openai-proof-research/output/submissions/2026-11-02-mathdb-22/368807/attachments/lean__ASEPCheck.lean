import ASEPData
import Mathlib.Data.List.Permutation
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Fin

/-! Decoder and Boolean checker for the per-tour certificates. -/

namespace ASEP

/-- `4 x*` as a function. -/
def XN (i j : Fin 8) : ℕ := (XNtab.getD i.val []).getD j.val 0

/-- Base-128 digits (little endian), `k` of them. -/
def digs : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => n % 128 :: digs k (n / 128)

/-- A decoded certificate: cyclic order `0 :: tl`, successor list `s`, a non-parallelism witness
`(a1,a2)`, `(b1,b2)` and a sparse integer direction `es`. -/
structure Cert where
  tl : List (Fin 8)
  s : List (Fin 8)
  a1 : Fin 8
  a2 : Fin 8
  b1 : Fin 8
  b2 : Fin 8
  es : List (Fin 8 × Fin 8 × ℤ)

def triples : ℕ → List ℕ → List (Fin 8 × Fin 8 × ℤ)
  | 0, _ => []
  | k + 1, a :: b :: c :: rest => (Fin.ofNat 8 a, Fin.ofNat 8 b, (c : ℤ) - 64) :: triples k rest
  | _ + 1, _ => []

def decodeDigits (d : List ℕ) : Cert :=
  { tl := (d.take 7).map (fun x => Fin.ofNat 8 x)
    s := ((d.drop 7).take 8).map (fun x => Fin.ofNat 8 x)
    a1 := Fin.ofNat 8 (d.getD 15 0), a2 := Fin.ofNat 8 (d.getD 16 0)
    b1 := Fin.ofNat 8 (d.getD 17 0), b2 := Fin.ofNat 8 (d.getD 18 0)
    es := triples (d.getD 19 0) (d.drop 20) }

def decode (N : ℕ) : Cert := decodeDigits (digs 90 N)

/-- successor of node `i` in the certificate's tour. -/
def Cert.succ (c : Cert) (i : Fin 8) : Fin 8 := c.s.getD i.val 0

/-- value of the direction at arc `(i,j)`. -/
def vZ (es : List (Fin 8 × Fin 8 × ℤ)) (i j : Fin 8) : ℤ :=
  ((es.filter (fun e => decide (e.1 = i ∧ e.2.1 = j))).map (fun e => e.2.2)).sum

/-- `4 (x* - T)` at arc `(i,j)`. -/
def dZ (c : Cert) (i j : Fin 8) : ℤ := (XN i j : ℤ) - 4 * (if c.succ i = j then 1 else 0)

def cutSum (es : List (Fin 8 × Fin 8 × ℤ)) (S : List (Fin 8)) : ℤ :=
  ((es.filter (fun e => decide (e.1 ∈ S ∧ e.2.1 ∉ S))).map (fun e => e.2.2)).sum

def tourCross (c : Cert) (S : List (Fin 8)) : ℕ :=
  ((Finset.univ : Finset (Fin 8)).filter (fun i => i ∈ S ∧ c.succ i ∉ S)).card

def chk (c : Cert) : Bool :=
  c.es.all (fun e => decide (e.1 ≠ e.2.1) && (decide (0 < XN e.1 e.2.1) || decide (c.succ e.1 = e.2.1))) &&
  (List.finRange 8).all (fun r => decide (((c.es.filter (fun e => decide (e.1 = r))).map (fun e => e.2.2)).sum = 0)) &&
  (List.finRange 8).all (fun r => decide (((c.es.filter (fun e => decide (e.2.1 = r))).map (fun e => e.2.2)).sum = 0)) &&
  tightCutList.all (fun S => decide (tourCross c S ≠ 1) || decide (cutSum c.es S = 0)) &&
  decide ((c.es.map (fun e => e.2.2.natAbs)).sum ≤ 64) &&
  decide (dZ c c.a1 c.a2 * vZ c.es c.b1 c.b2 ≠ dZ c c.b1 c.b2 * vZ c.es c.a1 c.a2) &&
  (List.range 8).all (fun k => decide (c.succ ((0 :: c.tl).getD k 0) = (0 :: c.tl).getD ((k + 1) % 8) 0))

def l7 : List (Fin 8) := [1, 2, 3, 4, 5, 6, 7]

end ASEP
