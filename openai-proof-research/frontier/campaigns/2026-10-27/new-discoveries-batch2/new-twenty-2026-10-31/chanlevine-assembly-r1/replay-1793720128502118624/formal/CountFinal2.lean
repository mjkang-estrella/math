import CountSpectralModel
namespace ChanLevine.Round3

/-- CONDITIONAL: the two explicit polynomial/count bridges remain open. -/
theorem spectralOrder (hc : TransferCountEvaluation) (hp : PrimitivePeriodData) :
    SpectralOrder := by
  intro n m _ hn hm k l hkl
  rw [hc n m hn hm k, hc n m hn hm l,
    transfer_quotient_eq n hp hn k m, transfer_quotient_eq n hp hn l m, hkl]

/-- CONDITIONAL; this is not an unconditional UnitCount certificate. -/
theorem unitCount (hc : TransferCountEvaluation) (hp : PrimitivePeriodData) :
    UnitCount := unitCount_of_spectralOrder (spectralOrder hc hp)
end ChanLevine.Round3
