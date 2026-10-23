#!/usr/bin/env python3
"""Prepare two mutually isolated, unchanged-scope independent review briefs."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p/'frontier/campaigns/2026-10-14'
o = b/'discovery-arithmetic-r162h-parent'
old = (b/'expanded-target-2026-10-17/fresh-arithmetic-r162h-brief.txt').read_text()
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = old.split(marker,1)[1]
assert len(suffix.encode()) == 5570
guards = old.split('Prospective isolation BEFORE FIRST filename traversal AND BODY SELECTION',1)[1].split('Catalogue access, if needed:',1)[0]
guards = 'Prospective isolation BEFORE FIRST filename traversal AND BODY SELECTION' + guards
iso = json.loads((o/'prospective-review-isolation.json').read_bytes())
for peer in iso['peer_original_initial_briefs']:
    data = (p/peer['brief']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == peer['brief_sha256'] and b'*arithmetic*r162*' in data
common = '''
Authorized Codex / GPT-6 Astra / high / default service tier. Campaign19/20,latestR041,one acceptance remains; no count is assigned by this review. Project /home/mj-kang/Documents/Dev/math/openai-proof-research. EVERY command workdir actual PROJECT root. Your unique root already exists empty; all notes/downloads/copies/temp/extract/render/control/scratch stay inside it. No outside/shared/author edits,git/staging/commit,nested agents,heavy installation,unbounded jobs or downstream formal/manuscript/release. Publication/uploads/submissions/contacts/browser UI STOPPED.

This is an INDEPENDENT FIRST review of an EXISTING unchanged frozen statement. The discovery/choose-family/freeze-new-theorem instructions in the preserved original standing brief are overridden for this assignment; all source-truth,scope,reading,rights and separate-gate rules still apply. Do not develop a weaker substitute or change the author theorem/proof. No prior independent review finding or author repair exists for this nominee; no desired-grade retry. The author claims a full proof but assigns no gate. Your review is independent of that claim.

Read direct AGENTS.md and sources/upstream.json completely, exact acceptance bytes[4801,6347) of frontier/NEW-TEN-2026-10-14.md, and the complete standing brief below. No ancestor search, journal/catalogue opening or whole-file decoding. Catalogue access, if needed, is ONLY binary seek/read sources/CONTENTS.md[123890,125448), Source072. Complete sources/preprints-tree.json is13223 entries,4858136bytes,SHAeeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b; ignore truncated tree.json. ALL source and operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate new deductions,scope and compatibility, not upstream truth.

NARROW DIRECT INPUT EXCEPTION, overriding broad r162 guards ONLY for this completed immutable author selection: frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162h/packet/ and its outside REPORT.md,MANIFEST.json,ANCHORS.json. You may read all files INSIDE that exact packet, including its original mathematical notes, selected canonical/primary/history bodies and metadata; do not widen to the containing campaign, linked excluded namespaces, author controls, another parent intake, or any peer review. Links are navigation only and do not confer body access. The author inputs are immutable. Hash/mode snapshot them before/after, without writing there.

Mandatory unchanged author identities:
packet/FROZEN-STATEMENT.md SHA2561d2799dba1c5bffca37724769974e56dc0e6c6ec2ac0196a01c3f15039ce6133,2064bytes.
packet/AUTHOR-PROOF.md SHA25692fe6bd2f718c85e558861588c3828dfdc039cff22f5e19fabcc67daa211db01,23791bytes.
packet/FINAL.md SHA25648c2adb91a7b865d1f1f6a0e9019323540f140f4de68d246b981e2959b12b66c.
MANIFEST.json SHA256a9224f1510ffad8d37c8861a4af0452788b0cedb720bbfbac3727836ff913365.
REPORT.md SHA256d2cd8891d46d949d60e9644960fccfea1471c43cfd62cf3d83e9d5b50dd2b328.
The60-file packet and25 canonical blobs matched parent artifact checks; that supplies no mathematical grade. Its dependency-free polynomial check is finite support only, not a theorem certificate.

Read the ENTIRE frozen statement,ENTIRE author proof,all three author notes,FINAL,REPORT and private/READING-ISOLATION.md. Read actual operative canonical proofs and strongest actual primary/original-history operations BEFORE extended verdict drafting. Both full Source072 textual proofs and actual includes are inside the admitted packet; authenticate all25 blobs against the complete tree and record actual semantic extents separately (23 texts,2 PDFs). Read the actual persistence primary operation, not just its name. The author read ELZ2002 Sections2--4 and Hedenmalm--Shimorin math/0406345v1 introduction/Section2 selectively; those are limits, not a clearance certificate for you. Determine and read what YOUR complete review requires, recover clipping/render missing formulas and disclose unavailable essential dependencies as INCOMPLETE rather than guessing. Strongest compatible operations can be paid even if the author's particular naive route fails.

Relevant exact ORIGINAL-history exceptions, by binary seek/read only: frontier/iterations/i135-complex-analysis-discovery.md[22410,25351) and[25351,35297), stopping at the next equal/higher heading. Copies and extent hashes are already inside the admitted packet. E_gamma/W2,subpower-gauge/boundary-measure/finite-tail and other earlier full endpoint targets remain unpaid; this theorem does NOT settle them. Additional authored-history selection must obey every prospective guard below before traversal AND body reads; no broader old scan rerun or excluded-body access. No exhaustive-search or priority claim.

Entire frozen scope to assess together: H is the upper half-plane; K is the FULL normalized injective holomorphic class,F(i)=0,F'(i)=1. For every beta in[3/4,1] and EVERY Borel probability P satisfying exact inverse-square affine covariance for ALL x in R,y>0 and nonnegative Borel tests Phi (including infinite integrals), one Borel model choice A:K->R union infinity, independent of P,beta,E,m, gives expected SQUARED compact C^m error <=C_(E,m)(1-beta)^(1/4) for EVERY nonempty compact E subset H and every finite derivative order m, with constants independent of P,beta. The SAME theorem includes uniqueness at beta=1 of the full Cauchy quadratic law, zero affine mass, and verification of covariance for every nonnegative Borel test. Do not assess only equality classification,nonvacuity,power-map subclasses,finite fibers or an unspecified modulus of continuity.

The author assumes EXACT covariance; critical-operator/eigenmeasure construction at rho=2, finite-scale extremizers,approximate-law stability and all earlier endpoint radial/weak/Lorentz/Orlicz targets remain outside this theorem and unpaid. Do not turn those unclaimed applications into repair requirements or use them to inflate contribution. Likewise routine equality-model algebra and finite persistence alone are not the whole proposed quantitative interface. All old frozen scopes and dispositions stay immutable, including r162g's countable-contact connector gap,Analytic157's paid full deformation,Arithmetic134's Jacquet/Levi gap and prior closed PASS/TECHNICAL results at zero count.

REVIEW ISOLATION: the two reviews start independently. Do not read/query/infer the OTHER review's entire root,brief,parent,copies,findings,status,activity or any derived alias, even if a completion arrives. Exclude *arithmetic*r162h-proof*,*arithmetic*162h-proof*,*arithmetic*r162h-contribution*,*arithmetic*162h-contribution* prospectively in ALL broad traversals; your OWN assigned root remains directly usable. Also exclude the entire discovery-arithmetic-r162h-parent namespace except the exact task prompt supplied here. Foreign Structural195 is only recorded-running under its owner; its ORIGINAL INITIAL *arithmetic*r162* literal covered both review namespaces before creation. Do not query its liveness or inspect its mathematics. All other literal guards and no-r twins below remain in force. This is prompt chronology, not OS/perfect isolation.

'''
common += guards
common += '''
Keep protected source/primary/history/search/extract/render/copied bodies AND named metadata private/local under original rights. Actual source/primary proofs and original-history extents,versions,late reads,truncations/recovery,false admissions/coarse omissions and access failures must be recorded honestly. Mathematics should dominate proportionate evidence work. Never claim semantic reading from paths,abstracts,hashes or another agent's reading claim. No larger administrative testing suite at the expense of the review.

Deliver a complete mathematical REVIEW with a full-scope verdict and integrated reasoning, plus dependencies and actual reading/isolation limits. Seal YOUR OWN exact selected packet once, with a fresh manifest, detached FINAL/MANIFEST/outside REPORT anchors, a read-only explicit-anchor verifier and proportionate tiny copied controls. Do not attach an inherited manifest to a reduced selection. These are artifact checks only. No self-acceptance,count,publication or downstream work. Preserve all author bytes/modes and all unrelated files. Parent alone adopts any later gate or requests a repair round.

'''
specs = {
 'proof': ('Arithmetic162h: independent full correctness review', '''Assess correctness of the ENTIRE unchanged frozen theorem and unchanged author proof, conditional ONLY on the stipulated true upstream inputs. Reconstruct all new arguments independently. Use PASS only if every frozen assertion follows and no essential verification remains; NEEDS_REPAIR for a necessary mathematical repair with exact location,reason and effect on frozen scope; INCOMPLETE for an essential unverified dependency or unresolved review obligation. Distinguish a proof gap from a counterexample to the theorem. Do not silently repair or weaken the statement. No contribution grade,acceptance or count.

Examine in particular: escape/good-target proof at beta<=1 without borrowing the rho>2 eigenmeasure construction; saddle topology and distinct rising components; oldest-component injectivity through infinite positive-superlevel exhaustion; uniform local Hessian gain; Borel connectivity/root/representative selection and affine covariance; exact fourth-power target weights,bad-target transfer,ordered expanding-box limits; moment identity and fourth moment; determinant-Laplacian sign and cutoff estimates; control of expected compact suprema; universal coefficient-circle projection including its center; all compact/m orders,nonvacuity and complete Cauchy-law uniqueness and all-Borel covariance. These are author interfaces to test, not prior findings or a demand for a predetermined verdict.'''),
 'contribution': ('Arithmetic162h: independent full substantial-contribution review', '''Assess substantial contribution for the ENTIRE unchanged frozen theorem, CONDITIONAL on its full correctness. This is separate from the other review: give no correctness PASS or repair verdict and do not wait for or inspect that review. Compare actual strongest compatible SOURCE,PRIMARY and ORIGINAL-HISTORY proof operations, not just exact theorem statements or terminology.

Use SUBSTANTIAL only if a specific closed nonroutine operation remains after the strongest integrated reduction and covers the entire frozen scope. Use TECHNICAL if compatible source/classical operations pay every frozen conclusion; in that case supply the actual integrated full derivation, including uniform exponent1/4,universal Borel model choice,all-law/compact/order quantifiers and complete critical classification. Naming persistence,Taylor,Cauchy or standard transport separately is not a substitute for checking their complete interface. Use INCOMPLETE if essential primary reading or a full-scope comparison remains unresolved. Do not grade a weaker equality statement or a fragment. A merely unproved named hard gap is not SUBSTANTIAL, and a source/classical composition is not made substantial by a new parameter label.

The proposed residual is quantitative component-persistence pairing on all good infinite fibers with Borel/affine compatibility, producing log gain cJ_+^3, surviving exact fourth-power transport to E J_+^4<=C(1-beta), followed by the determinant-Laplacian/cutoff route to one universal compact-analytic quadratic approximation and the complete critical law. Test whether this ENTIRE operation is already paid by actual source pairing/transport and primary persistence/analytic mechanisms, or identify precisely what is not. The author acknowledges the individual persistence rule,source transport,standard analytic estimates and equality algebra as paid. The exact covariance hypothesis and excluded critical-operator applications may not be silently upgraded. No worldwide priority or exhaustive literature claim is required or justified.''')
}
prepared = []
old_tokens = set(re.findall(r'\*[^\s,;()]*\*', old))
for role,(title,focus) in specs.items():
    root = b/f'arithmetic-r162h-{role}-r1'
    brief_path = b/f'expanded-target-2026-10-17/arithmetic-r162h-{role}-brief-r1.txt'
    assert not root.exists() and not brief_path.exists()
    text = title + '\nWrite ONLY '+root.relative_to(p).as_posix()+'/\n\n'+focus+'\n'+common+marker+suffix
    assert old_tokens <= set(re.findall(r'\*[^\s,;()]*\*',text))
    assert text.split(marker,1)[1] == suffix
    root.mkdir()
    brief_path.write_text(text)
    prepared.append({'role':role,'title':title,'root':root.relative_to(p).as_posix()+'/', 'brief':brief_path.relative_to(p).as_posix(),'bytes':len(text.encode()),'sha256':hashlib.sha256(text.encode()).hexdigest(),'standing_brief_bytes':5570,'old_literal_guards_retained':len(old_tokens),'frozen_scope_sha256':'1d2799dba1c5bffca37724769974e56dc0e6c6ec2ac0196a01c3f15039ce6133','author_proof_sha256':'92fe6bd2f718c85e558861588c3828dfdc039cff22f5e19fabcc67daa211db01'})
(o/'review-preparation.json').write_text(json.dumps(prepared,indent=2)+'\n')
print(json.dumps(prepared,indent=2))
