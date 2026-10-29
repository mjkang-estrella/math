from pathlib import Path
import json,hashlib,re
L=Path(__file__).resolve().parent;P=L/'packet';V=L/'verification-final'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((V/'verification-receipt.json').read_text());assert r['declaration_count']==167 and r['pdf_byte_identical'] and r['zip_byte_identical']
h=json.loads((L/'final-helper.log').read_text().strip().splitlines()[-1]);assert h['guard_exit']==0 and h['reason'] is None
prov=json.loads((P/'provenance.json').read_text());prov['final_fresh_replay']={'archive_sha256':sha(L/'edge-irregulator-manuscript-packet.zip'),'paper_sha256':sha(P/'paper.pdf'),'manifest_sha256':sha(P/'manifest.json'),'verification_receipt_sha256':sha(V/'verification-receipt.json'),'proof_modules':r['proof_modules'],'declarations':r['declaration_count'],'axiom_union':r['axiom_union'],'max_lean_group_rss_kib':max(x['peak_group_rss_kib'] for x in r['steps']),'helper_group_rss_bytes':h['sampled_peak_group_rss'],'wall_seconds':h['wall_seconds'],'pdf_and_zip_byte_identical':True,'both_audit_logs_byte_identical':True,'root_final_review':'PENDING'}
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
(L/'archive-sha256.txt').write_text(sha(L/'edge-irregulator-manuscript-packet.zip')+'  edge-irregulator-manuscript-packet.zip\n')
f=prov['final_fresh_replay'];counts=prov['per_module_counts']
text=f'''# Final implementation result — 29 October 2026

Completed SOLO within the assigned lane. Candidate credit 0; campaign remains
7/30 additional, 37/60 accepted. No git, shared/other-lane writes, child agents,
browser/account writes, external posting, acceptance or count edit.

## Mathematical deliverable

Thirteen inherited mathematical modules verified byte-identical, including all
five common sources. Three new declarations in Result.lean close minimum_exact,
fin_minimum_exact via minimum_iso, and main. For each natural t≥2 the original
graph is connected, has 6t+1 vertices, 8t edges and exact minimum 3t; the Fin
model has the same exact minimum, and SourceClaim is negated. No conditional
placeholder, residual proof bridge or t=1 optimum claim. Retained degrees are
recomputed. The four-page paper explicitly proves every diamond boundary case,
path charge, edge-disjoint summation, attaining witness and real-constant negation.

## Fresh extracted verification within this lane

All 14 mathematical modules plus both audits strictly rebuilt serially from no
own prebuilt artifacts. Exhaustive actual-origin inventory: 167 unique actual
declarations, including generated/private names. Counts by origin:

{json.dumps(dict(sorted(counts.items())),sort_keys=True)}

All actual types, safety flags and transitive axiom closures checked; all unsafe,
partial and axiom flags false. Axiom union: {', '.join(r['axiom_union'])}.
Both complete audit logs matched byte-identically. Lean binary, all nine package
revisions and all 1132 imported package hashes checked. Final PDF and deterministic
source-only ZIP rebuilt byte-identically from the final archive's fresh extraction.
No own prebuilt oleans/ileans/IR/object libraries are in the ZIP.

Lean final replay sampled peak group RSS: {f['max_lean_group_rss_kib']} KiB
({f['max_lean_group_rss_kib']/1024:.2f} MiB). Helper group sampled peak:
{f['helper_group_rss_bytes']} bytes ({f['helper_group_rss_bytes']/1024**2:.2f} MiB).
Final wrapper wall: {f['wall_seconds']:.3f}s. No guard kill/cap raise. Limits:
helper AS/groupRSS512MiB, CPU210/wall230, BLAS1; Lean -j1 -M2700,
warningAsError/autoImplicit=false, groupRSS2800MiB, CPU210/wall230,
AS infinity only Lean child; nominal sampling40/45ms. Unsampled transients and
OS scheduling delays cannot be excluded. Receipts retain actual per-step values.

## Exact hashes

- Final ZIP SHA256: {f['archive_sha256']}
- Paper PDF SHA256: {f['paper_sha256']}
- Source manifest SHA256: {f['manifest_sha256']}
- Final verification receipt SHA256: {f['verification_receipt_sha256']}
- Lower input ZIP SHA256: a94a75354404e27c827dca92c13da7b87df806ec6bda6abd8254376825c520a6
- Upper input ZIP SHA256: 4d62461a62577e5b2d77045eb2d228814c7481c90b24d45d85383c0313e2d641
- Publisher PDF SHA256: 574aaf95e9d6e94273d2ebc15704bb1209537625d7e59b5282d9a130efb1ceae

PDF marker executed exactly once before authoring. Every final page (1–4) was
rendered and personally visually inspected, with no clipping, overlapping or
overfull boxes; page renders remain in render/. Attribution follows established
campaign Research manuscript wording; Codex preparation is disclosed, no person
inferred. Source: Bensmail, Catherinot, Fioravantes, Marcille, Oijid, WALCOM2026,
353–367, DOI10.1007/978-981-95-7127-7_24, Conj1 printed356, actual page inspected.
No retained connectivity or minimum-degree assumption is imported.

## Reproduce and remaining gates

Run `sh packet/build.sh "$PWD/edge-irregulator-manuscript-packet.zip" "$PWD/new-extraction"`
from this lane, choosing a nonexistent destination. Build is pinned to the existing
Lean/Mathlib/Tectonic/cache environment; it does not vendor that entire toolchain.
The archive includes PDF/TeX, exact formal sources, pins, complete audit and verifier,
provenance, inherited failure evidence and root/source review pointers.

Existing bounded source/prior review dated2026-10-29 is recorded, not replaced.
No worldwide-priority claim or new novelty clearance. Separate final independent
ROOT review, final root current-prior refresh/adjudication and root-only acceptance
remain. The implementation replay status applies only to work in this lane.

Inherited early lower receipt overwrite and upper helper supervision deviations
are preserved. Initial own copied helper supervisors capped payloads but did not
explicitly self-limit AS/CPU/alarm; those self limits were added before packaging
and both complete fresh replays. Earlier supervisor self-limit compliance is not
claimed. Own failed Result/AuditPrint sources, logs and receipts are retained;
initial missing TeX/font/cache and overflow failures are disclosed in provenance.
No failed attempt is treated as a checked theorem.
'''
(L/'FINAL-RESULT.md').write_text(text)
print(json.dumps(f,indent=2))
