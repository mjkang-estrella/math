# Failures and access limits

- Initial freeze failed with TypeError because r304's manifest is a list. Failed helper and log preserved. Corrected schema handling passed without changing upstream.
- No network fetch failed in this lane. Fifty primary and four successor arXiv HTML endpoints returned bodies. Unversioned request endpoints are distinguished from observed body versions in the separate catalogue. No 403/429 retry occurred.
- MathDB: inherited 429 HOLD, zero requests. AIM/Kourovka/EGRES, AIProofWatch, rigid-body and triangle-gap denied routes remain parked; no re-probe or alternate-route fishing.
- Current public proof registry heads, exact scopes and chronology remain unverified. No public novelty clearance for any ID.
- Automatic passage selection sometimes picked a mention or failed its exact pattern. These failures are retained in the logs and passage JSON; a selected locator is not automatically a read question. Supplementary inspected passages improve coverage without asserting complete body/dependency audits.
- Broad external searches returned incidental MathDB, ScienceDirect and registry results; no such result page was opened or used as proof evidence. Mathematical claims rely on retained primary sources and literal assigned statements.
- No full proof certificate, Lean endpoint, independent scientific acceptance review, or paper was produced. The finite orbit check is strictly limited and not credited.
