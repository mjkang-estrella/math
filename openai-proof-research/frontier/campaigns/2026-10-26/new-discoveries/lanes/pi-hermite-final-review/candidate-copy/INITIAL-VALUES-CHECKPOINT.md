# Source initial values completed: 52 supporting declarations / four modules

InitialValues.lean adds19 declarations to the earlier33. It compiles cleanly with
warningAsError=true; all4 module logs are empty. All52 actual types/axioms have
been printed and read by the parent, using only propext,Classical.choice,Quot.sound.
Evidence: formal/initial-values-build.json, initial-values-axioms.log and
AllInitialChecks.lean. This is supporting formal progress, NOT a full source
conjecture proof or a discovery credit. Accepted tally is25/30.

New literal bridges:
- Source Gamma coefficient positivity, values at0 and1, exact add-two recurrence.
- Physical Hermite value and slope at0 for both parities, with exact source
  Gamma coefficient rather than an assumed factorial normalization.
- Even initial energy identity and the unconditional literal source_bulk_even
  for every m and0<=x,square(x)<4m+1. This known even subcase is uncredited.
- Odd slope magnitude positivity and recurrence; its exact squared ratio to
  sourceCoefficient(2m+1)^2 is the actual Wallis-product oddEnergyRatio.
- Both required odd initial bounds: A^2<=99/98 * E C^2 for m>=1, and the strict
  corrected-energy inequality A^2(1-1/(2E^2))<E C^2 for every m.

The odd ratio bridge uses the true Gamma recurrence and matching recurrences
of source initial values/Wallis products. No factorial or Gamma identity is
assumed. The existing frozen SourceDefs/Energy/WallisBounds bytes are unchanged;
the Pi implementation can continue against its assigned exact copies.

Remaining formal work: generic odd sine comparison and energy loss (assigned
to a separate Pi implementation lane), pre-x0 bound and source assembly,
n=1 branch, and a sufficient global clamped-tail theorem. The mathematical
argument invokes the classical Cramer--Indritz/DLMF18.14.9 inequality, which is
not yet encoded in Lean. No unproved classical axiom will be imported silently.

The original19-file mathematical review freeze and33-declaration checkpoint are
unchanged. This document supersedes ONLY their earlier missing-initial-values
scope. The running preliminary reviewer judges the full mathematical proof,
source, bounded novelty and substantive eligibility; it does not provide a
final formal/manuscript verdict. No paper/packet/count exists for Hermite yet.

Tail-source access: official DLMF18.14.9 was read and cites Szász1951, J. Indian
Math. Soc.15pp129--134. This reference is distinct from Indritz1961, whose AMS
body was403-blocked. The Szász DOI/publisher legacy route leads to a migrated
frontend; observed public metadata API searches did not retrieve the target.
No Szász theorem body has been read or treated as a verified source. The
public frontend scripts used only to locate that read-only API are not mathematical
evidence. Failed metadata search is not a novelty certificate or global access claim.
