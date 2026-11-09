import CountTransfer
namespace ChanLevine

theorem rotationCount : RotationCount := rotationCount_proof

theorem arithmeticOrbit : ArithmeticOrbit := arithmeticOrbit_proof

/-- CONDITIONAL ONLY: SpectralOrder is still unproved. -/
theorem unitCount (hs : SpectralOrder) : UnitCount := unitCount_of_spectralOrder hs
end ChanLevine
