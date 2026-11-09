import CountR4Period
namespace ChanLevine.Round4
/-- CONDITIONAL handback: count evaluation and top coefficient are still open. -/
theorem spectralOrder (hc : Round3.TransferCountEvaluation) (ht : PrimitiveTopCoefficient) :
    SpectralOrder := Round3.spectralOrder hc (primitivePeriodData ht)
/-- CONDITIONAL handback, not an unconditional certificate. -/
theorem unitCount (hc : Round3.TransferCountEvaluation) (ht : PrimitiveTopCoefficient) :
    UnitCount := unitCount_of_spectralOrder (spectralOrder hc ht)
end ChanLevine.Round4
