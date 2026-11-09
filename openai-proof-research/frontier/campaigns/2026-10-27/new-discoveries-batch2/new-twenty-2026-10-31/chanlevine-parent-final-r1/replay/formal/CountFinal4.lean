import CountR5Fibre
namespace ChanLevine.Round5
/-- Unconditional: all one-period algebraic data are now proved. -/
theorem primitivePeriodData : Round3.PrimitivePeriodData :=
  Round4.primitivePeriodData primitiveTopCoefficient
/-- Partial handback: exactly the literal counting/transfer bridge remains. -/
theorem spectralOrder (hc : Round3.TransferCountEvaluation) : SpectralOrder :=
  Round3.spectralOrder hc primitivePeriodData
/-- Partial handback, conditional on the same single counting bridge. -/
theorem unitCount (hc : Round3.TransferCountEvaluation) : UnitCount :=
  unitCount_of_spectralOrder (spectralOrder hc)
end ChanLevine.Round5
