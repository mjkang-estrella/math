import CountRotation
import Mathlib.Data.ZMod.Units
namespace ChanLevine
set_option backward.isDefEq.respectTransparency false in
theorem unit_mul_gcd {N : ℕ} [NeZero N] (a : ZMod N) :
    ∃ u : (ZMod N)ˣ, a = (u : ZMod N) * (a.val.gcd N : ℕ) := by
  let d := a.val.gcd N
  change ∃ u : (ZMod N)ˣ, a = (u : ZMod N) * (d : ℕ)
  have hd : d ≠ 0 := Nat.gcd_ne_zero_right (NeZero.ne N)
  obtain ⟨a₀, (ha₀ : _ = d * _)⟩ := a.val.gcd_dvd_left N
  obtain ⟨N₀, (hN₀ : _ = d * _)⟩ := a.val.gcd_dvd_right N
  have hu₀ : IsUnit (a₀ : ZMod N₀) := by
    refine (ZMod.isUnit_iff_coprime _ _).mpr (Nat.isCoprime_iff_coprime.mp ?_)
    obtain ⟨p, q, hpq⟩ : ∃ (p q : ℤ), d = a.val * p + N * q :=
      ⟨_, _, Nat.gcd_eq_gcd_ab _ _⟩
    rw [ha₀, hN₀, Nat.cast_mul, Nat.cast_mul, mul_assoc, mul_assoc, ← mul_add,
      eq_comm, mul_comm _ p, mul_comm _ q] at hpq
    exact ⟨p, q, Int.eq_one_of_mul_eq_self_right (Nat.cast_ne_zero.mpr hd) hpq⟩
  obtain ⟨u, hu⟩ := (ZMod.unitsMap_surjective
    (⟨d, mul_comm d N₀ ▸ hN₀⟩ : N₀ ∣ N)) hu₀.unit
  rw [ZMod.unitsMap_def, ← Units.val_inj, Units.coe_map, IsUnit.unit_spec,
    MonoidHom.coe_coe] at hu
  refine ⟨u, ?_⟩
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val u.1, ha₀,
    ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff, mul_comm _ d, Nat.ModEq]
  simp only [hN₀, Nat.mul_mod_mul_left, Nat.mul_right_inj hd]
  rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff, ← hu,
    ZMod.natCast_val, ZMod.castHom_apply]

theorem gcd_unit_orbit {d : ℕ} [NeZero d] (i j : ZMod d)
    (h : Nat.gcd d i.val = Nat.gcd d j.val) :
    ∃ u : (ZMod d)ˣ, j = (u : ZMod d) * i := by
  obtain ⟨u, hu⟩ := unit_mul_gcd i
  obtain ⟨v, hv⟩ := unit_mul_gcd j
  refine ⟨v * u⁻¹, ?_⟩
  rw [hu, hv, Nat.gcd_comm j.val d, ← h, ← Nat.gcd_comm i.val d]
  simp [mul_assoc]

theorem gcd_kernel_multiple (n m : ℕ) [NeZero n] (z : ZMod n)
    (h : (z.val : ZMod (Nat.gcd n m)) = 0) :
    ∃ b : ℕ, z = (b*m : ℕ) := by
  have hd : Nat.gcd n m ∣ z.val := (CharP.cast_eq_zero_iff (ZMod (Nat.gcd n m)) (Nat.gcd n m) z.val).mp h
  obtain ⟨c, hc⟩ := hd
  have hb : (Nat.gcd n m : ZMod n) = (m : ZMod n) * (Nat.gcdB n m : ℤ) := by
    have he := congrArg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab n m)
    simpa using he
  let t : ZMod n := (c : ZMod n) * (Nat.gcdB n m : ℤ)
  refine ⟨t.val, ?_⟩
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    z = (z.val : ZMod n) := (ZMod.natCast_zmod_val z).symm
    _ = (Nat.gcd n m : ZMod n) * c := by rw [hc, Nat.cast_mul]
    _ = t * m := by rw [hb]; dsimp [t]; ring

theorem arithmeticOrbit_proof : ArithmeticOrbit := by
  intro n m _ _ _ i j h
  let d := Nat.gcd n m
  have hd : d ∣ n := Nat.gcd_dvd_left n m
  have : NeZero d := ⟨Nat.gcd_ne_zero_left (NeZero.ne n)⟩
  let f : ZMod n →+* ZMod d := ZMod.castHom hd (ZMod d)
  have hf (a : ZMod n) : f a = (a.val : ZMod d) := by
    change a.cast = (a.val : ZMod d)
    exact (ZMod.natCast_val a).symm
  have hg (a : ZMod n) : Nat.gcd d (f a).val = Nat.gcd d a.val := by
    rw [hf, ZMod.val_natCast]
    simpa [Nat.gcd_comm] using (Nat.gcd_rec d a.val).symm
  obtain ⟨v, hv⟩ := gcd_unit_orbit (f i) (f j) (by rw [hg, hg]; exact h)
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd v
  have huv : f (u : ZMod n) = (v : ZMod d) := by
    exact congrArg Units.val hu
  have hz : ((j - (u : ZMod n)*i).val : ZMod d) = 0 := by
    rw [← hf, map_sub, map_mul, huv, hv, sub_self]
  obtain ⟨b, hb⟩ := gcd_kernel_multiple n m (j - (u : ZMod n)*i) hz
  exact ⟨u, b, by rw [← hb]; ring⟩
end ChanLevine
