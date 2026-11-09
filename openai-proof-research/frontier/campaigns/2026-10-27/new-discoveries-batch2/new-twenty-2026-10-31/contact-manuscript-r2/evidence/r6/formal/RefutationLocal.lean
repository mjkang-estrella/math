import BidiskCertificate
import LocalBidiskContact
import ContactUniqueness
namespace ContactPilot

theorem bidisk_not_local_contact_two :
    ¬ HasLocalZeroSetContact (eval₂ bidiskNumerator) (-1) 1 2 := by
  intro h
  have he := local_contact_unique h bidisk_local_contact_six
  norm_num at he

theorem refutationLocal : ¬ SourceConjectureLocal := by
  intro h
  have he := h 5 candidateGraph candidateColors 0 candidateCertificate 1 6
    nearest_w_one (by norm_num) (by norm_num) bidisk_local_contact_six
  norm_num at he
end ContactPilot
