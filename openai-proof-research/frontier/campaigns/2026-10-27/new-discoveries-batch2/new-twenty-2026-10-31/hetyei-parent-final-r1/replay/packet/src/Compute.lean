import Bridge
namespace Hetyei347230
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem check_I2u : ((I2L uList).all fun p => p.1.length == 5) = true ∧
    ((allWords 5).all fun w => coeffL (I2L uList) w == 0) = true := by
  constructor <;> decide +kernel
theorem I2_uCert : I2 uCert = 0 := by
  rw [uCert, I2_toPoly]
  obtain ⟨h5, hz⟩ := check_I2u
  apply toPoly_eq_zero_of_coeff _ (allWords 5)
  · intro p hp
    have hh : p.1.length = 5 := by simpa using List.all_eq_true.mp h5 p hp
    simpa [hh] using allWords_complete p.1
  · intro w hw
    simpa using List.all_eq_true.mp hz w hw
end Hetyei347230
