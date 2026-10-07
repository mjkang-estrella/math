import Research.Goals

/-!
Negative specification tests from the independent Opus audit (wave 1).
These deliberately supply inadmissible secret-revealing encodings. They are
not ECDLP algorithms or improvements. The noncomputable relabeling below
exposes an unchecked field of the interface; its encoding is not executed
or charged by the machine. None of the core definitions is changed here.
-/
namespace Research.EncodingAudit

def decodeBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * decodeBits bs

theorem decode_bits (w v : Nat) : decodeBits (bits w v) = v % 2 ^ w := by
  induction w generalizing v with
  | zero => simp [bits, decodeBits, Nat.mod_one]
  | succ w ih =>
    simp only [bits, decodeBits, ih]
    rw [Nat.pow_succ', Nat.mod_mul]
    split <;> simp_all <;> omega

theorem length_bits (w v : Nat) : (bits w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [bits, ih]

theorem read_cons (L : List Bool) (b : Bool) (bs : List Bool) :
    ({ left := L, head := b, right := bs } : Machine.Tape).read (bs.length + 1) = b :: bs := by
  induction bs generalizing L b with
  | nil => rfl
  | cons c cs ih =>
    simp only [Machine.Tape.read, Machine.Tape.moveRight, List.length_cons] at ih ⊢
    exact congrArg (b :: ·) (ih _ _)

theorem read_ofBits (l : List Bool) : (Machine.Tape.ofBits l).read l.length = l := by
  cases l with
  | nil => rfl
  | cons b bs => exact read_cons [] b bs

def succMod (n : Nat) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨(x.val + 1) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

theorem iter_val (n k : Nat) :
    (iteratePoint (succMod n) ⟨0, Nat.two_pow_pos n⟩ k).val = k % 2 ^ n := by
  induction k with
  | zero => simp [iteratePoint]
  | succ k ih => simp [iteratePoint, succMod, ih, Nat.add_mod]

/-- A legal `CyclicProblem` whose public-key encoding IS the secret. -/
def leaky (n : Nat) : CyclicProblem where
  Point := Fin (2 ^ n)
  order := 2 ^ n
  order_pos := Nat.two_pow_pos n
  zero := ⟨0, Nat.two_pow_pos n⟩
  next := succMod n
  wraps := by apply Fin.ext; simp [iter_val]
  distinct := by
    intro a b h
    have := congrArg Fin.val h
    simp only [iter_val, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
    exact Fin.ext this
  encodePoint := fun x => bits n x.val
  encode_injective := by
    intro a b h
    have := congrArg decodeBits h
    simp only [decode_bits, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
    exact Fin.ext this
  parameters := []
  outputWidth := n
  fits := Nat.le_refl _

theorem leaky_solved (n : Nat) : SolvesWithin (leaky n) [.halt] 0 := by
  intro d
  refine ⟨Machine.Tape.ofBits ((leaky n).input d), rfl, ?_⟩
  have hk : (leaky n).input d = bits n d.val := by
    simp only [CyclicProblem.input, CyclicProblem.publicKey, leaky, List.nil_append]
    congr 1
    rw [iter_val]; exact Nat.mod_eq_of_lt d.isLt
  have := read_ofBits ((leaky n).input d)
  rw [hk, length_bits] at this
  show (Machine.Tape.ofBits ((leaky n).input d)).read n = _
  rw [hk]; exact this

def leakyFamily : ProblemFamily where
  problem := leaky
  order_lower := fun _ => Nat.le_refl _
  order_upper := fun n => Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n)

/-- The "strong breakthrough target" is a theorem for this legal family. -/
theorem breakthrough_trivial : ExponentBreakthrough leakyFamily :=
  ⟨[.halt], fun _ => 0, fun n => leaky_solved n, 1, 1, 0, by decide, by decide,
    fun n _ => by simp⟩

theorem concrete_trivial : ConcreteGoal (leaky 256) 3 0 :=
  ⟨[.halt], by decide, leaky_solved 256⟩

/-- Keep the SAME point type, order, zero and `next` (e.g. a genuine curve
orbit) but replace only the encoding and parameters. -/
noncomputable def relabel (P : CyclicProblem) : CyclicProblem :=
  { P with
    encodePoint := fun x => by
      classical
      exact if h : ∃ d : Fin P.order, iteratePoint P.next P.zero d.val = x
        then true :: bits P.outputWidth (Classical.choose h).val
        else false :: P.encodePoint x
    encode_injective := by
      classical
      intro a b hab
      by_cases ha : ∃ d : Fin P.order, iteratePoint P.next P.zero d.val = a
      · by_cases hb : ∃ d : Fin P.order, iteratePoint P.next P.zero d.val = b
        · rw [dite_eq_left ha, dite_eq_left hb, List.cons.injEq] at hab
          have e : (Classical.choose ha).val = (Classical.choose hb).val :=
            bits_inj P.outputWidth _ _
              (by have := P.fits; have := (Classical.choose ha).isLt; omega)
              (by have := P.fits; have := (Classical.choose hb).isLt; omega) hab.2
          rw [← Classical.choose_spec ha, ← Classical.choose_spec hb, e]
        · rw [dite_eq_left ha, dite_eq_right hb, List.cons.injEq] at hab; exact absurd hab.1 (by decide)
      · by_cases hb : ∃ d : Fin P.order, iteratePoint P.next P.zero d.val = b
        · rw [dite_eq_right ha, dite_eq_left hb, List.cons.injEq] at hab; exact absurd hab.1 (by decide)
        · rw [dite_eq_right ha, dite_eq_right hb, List.cons.injEq] at hab; exact P.encode_injective a b hab.2
    parameters := [] }
where
  bits_inj : ∀ w x y, x < 2 ^ w → y < 2 ^ w → bits w x = bits w y → x = y := by
    intro w
    induction w with
    | zero => intro x y hx hy _; simp at hx hy; omega
    | succ w ih =>
      intro x y hx hy h
      simp only [bits, List.cons.injEq] at h
      have h2 := ih (x / 2) (y / 2) (by rw [Nat.pow_succ] at hx; omega)
        (by rw [Nat.pow_succ] at hy; omega) h.2
      have : x % 2 = y % 2 := by
        rcases Nat.mod_two_eq_zero_or_one x with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one y with h3 | h3 <;> simp_all
      omega

theorem relabel_solved (P : CyclicProblem) : SolvesWithin (relabel P) [.right 1, .halt] 1 := by
  classical
  intro d
  have hd : d.val < P.order := d.isLt
  have hex : ∃ e : Fin P.order, iteratePoint P.next P.zero e.val =
      iteratePoint P.next P.zero d.val := ⟨⟨d.val, hd⟩, rfl⟩
  have hc : (Classical.choose hex).val = d.val :=
    congrArg Fin.val (P.distinct (Classical.choose hex) ⟨d.val, hd⟩ (Classical.choose_spec hex))
  have hin : (relabel P).input d = true :: bits P.outputWidth d.val := by
    show [] ++ (relabel P).encodePoint (iteratePoint P.next P.zero d.val) = _
    simp only [List.nil_append, relabel]
    rw [dite_eq_left hex, hc]
  refine ⟨_, rfl, ?_⟩
  show Machine.Tape.read _ P.outputWidth = bits P.outputWidth d.val
  rw [hin]
  have hl := length_bits P.outputWidth d.val
  cases hb : bits P.outputWidth d.val with
  | nil => rw [hb] at hl; rw [← hl]; rfl
  | cons b bs =>
    rw [hb] at hl; rw [← hl]
    exact read_cons _ b bs


end Research.EncodingAudit
