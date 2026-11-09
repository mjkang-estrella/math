import Nut
namespace Nut8.CertificateBench
/-- Executable Laplace expansion. The bridge to Matrix.det is NOT supplied. -/
noncomputable def detFuel : Nat → List (List Int) → Int
  | 0, _ => 1
  | _+1, [] => 0
  | n+1, r :: rs => ((List.range r.length).map fun j =>
      if r[j]! = (0 : Int) then (0 : Int) else
      (if j % 2 = 0 then 1 else -1) * r[j]! *
        detFuel n (rs.map (fun row => row.eraseIdx j))).sum

theorem sampleInvertible : detFuel 8 [[1, 0, 0, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0, 0]] = 48 := by
  decide +kernel

theorem sampleCofactor : detFuel 7 [[2, 0, 0, 0, 0, 1, 0], [0, -2, 0, 0, 0, 1, 0], [0, 0, -2, 0, 0, 0, 1], [0, 0, 0, -2, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1], [1, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0]] = 0 := by
  decide +kernel

end Nut8.CertificateBench
