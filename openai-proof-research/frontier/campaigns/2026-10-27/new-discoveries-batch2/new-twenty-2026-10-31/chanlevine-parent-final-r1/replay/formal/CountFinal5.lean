import CountR6Bridge
namespace ChanLevine.Round6
/-- Partial handback: both displayed finite identities remain explicit premises. -/
theorem spectralOrder (hc : MatchingCountConvolution) (ht : MatchingTraceExpansion) :
    SpectralOrder := Round5.spectralOrder (transferCountEvaluation hc ht)
/-- Partial handback; this is not an unconditional UnitCount proof. -/
theorem unitCount (hc : MatchingCountConvolution) (ht : MatchingTraceExpansion) :
    UnitCount := unitCount_of_spectralOrder (spectralOrder hc ht)
end ChanLevine.Round6
