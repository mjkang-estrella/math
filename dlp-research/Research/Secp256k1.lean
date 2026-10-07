import Std

/-! Standard constants only. Scalar multiplication, exact generator order,
point encoding, and a connection to CyclicProblem remain unimplemented.
No statement in this module asserts hardness or a working attack. -/
namespace Research.Secp256k1

def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
def gx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def gy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def AffineOnCurve (x y : Nat) : Prop :=
  x < p ∧ y < p ∧ (y * y) % p = (x * x * x + 7) % p

instance (x y : Nat) : Decidable (AffineOnCurve x y) :=
  inferInstanceAs (Decidable (x < p ∧ y < p ∧ (y * y) % p = (x * x * x + 7) % p))

theorem generator_on_curve : AffineOnCurve gx gy := by
  decide +kernel

theorem scalar_fits_256_bits : n < 2 ^ 256 := by
  decide +kernel

end Research.Secp256k1
