# Literal Rényi threshold endpoint

The unconditional density-level endpoint is proved. Root review and integration remain separate. Credit zero; campaign counts unchanged at 8/38. No paper, acceptance, optimizer characterization or worldwide-priority claim. Work was solo, confined to this lane, without children, git operations, browser, external messages, publishing or package mutation.

## Source and reuse

Fu–Li arXiv:2510.09206v3, printed p.2, unnumbered paragraph after (1.2), frozen HTML S1.p6.1, https://arxiv.org/html/2510.09206v3. Its actual paragraph was read from the inherited HTML: it suspects p0 in (0,1) with exponential maximization for p>=p0. This is NOT Shannon Conjecture 1.1. The necessary consequence here uses dimension one, p0<p<1 and the rate-one exponential. No all-rate invariance, cube result, explicit cofinal witnesses, random-variable scaffolding or actual optimizer claim is made.

The ordinary proof is sol-fresh-source-discovery-r111/PROOF.md, SHA256 ca72b385e83d919fbaa97af4d55f0e7d00e949c01c8c4af07fd93ef30fef977a. Root DECISION.md and ADOPTION.json were read. No new novelty investigation was undertaken; root owns the existing bounded clearance and limitations. No corpus/audit inventory was copied.

Inherited archive SHA256: 9c7ea1f4c4bb76ad5f3be5d0ac8d890f3dbf085a871ae31e5dde67178e1d5737. All root-freeze entries were verified before development. The archive was extracted here. All eight inherited mathematical modules, original OriginAudit, guards and pins remain byte-identical. frozen-before.json holds the root freeze; verify_frozen.py checks every original and the local inherited source bytes during delivery and fresh replay. Only the inherited necessary proof/review/HTML inputs were retained.

## Definitions and exact interfaces

All definitions are in namespace Renyi; all integrals are real Lebesgue integrals. Existing definitions are unchanged: normalizer(a)=(1-exp(-a))^-1; density a is the literal Icc 0 a indicator of normalizer(a)*exp(-x); exponential is the Ici 0 indicator of exp(-x); convolution f g s is the integral of f(t)g(s-t); moment p f is integral f(x)^p; entropy p f=log(moment p f)/(1-p). LogConcaveDensity requires global nonnegativity and the usual multiplicative inequality for every open weight 0<t<1 (endpoint weights give equality).

Deficit.Ja p a is defined directly as integral over Ioi 0 of exp(-p*s)*(tent a s)^p, not from the desired deficit. For every a>0,p>0:

    deficit_identity : J p - Ja p a = exp(-p*a)*tail p a
    convolution_moment : moment p (convolution (density a) (density a))
                           = normalizer a^(2*p)*Ja p a

profile_integrable proves whole-line integrability from actual compact support. convolution_power_profile proves the pointwise identity with normalizer^(2*p). profile_integral removes the nonpositive half-line where the profile vanishes. The deficit proof uses integrable subtraction, restricts the difference from Ioi 0 to Ioi a because it vanishes on (0,a], and proves s=a+u via translation invariance of the actual indicator integral. The shifted tent is max(a-u,0). There is no assumed substitution, interval splitting or endpoint bridge; a is included in the zero difference region. The identity needs only p>0, while the inherited cutoff also needs p<1.

Baseline proves nonnegativity, global log-concavity, integrability and integral one of exponential. exponential_convolution_integrand identifies the integrand on Icc 0 s and proves it integrable for every s. exponential_convolution evaluates the literal convolution as the Ici 0 indicator of exp(-s)*s. For every p>0 it proves integrability of both power functions, input moment=1/p, output moment=J p>0, and exponential_ratio=p*J p. Input positivity is proved in exponential_admissible. Ici/Ioi endpoints use null singletons explicitly.

Endpoint.strict_ratio, for a>0,p>0,tail p a<J p, proves:

    p*J p < moment p (convolution (density a) (density a)) / moment p (density a)

It retains the inherited input formula normalizer(a)^p*(1-exp(-pa))/p, and proves normalizer(a)>=1. entropy_increment_ratio proves the entropy difference equals log of the positive moment ratio divided by 1-p.

Admissible p f explicitly requires everywhere nonnegative f, LogConcaveDensity f, Integrable f, integral f=1, integrable input p-power with positive moment, integrable convolution integrand for every s, everywhere nonnegative convolution, and integrable output p-power with positive moment. density_admissible and exponential_admissible prove every one of these facts for the actual witnesses.

every_order_counterexample (hp:0<p) (hp1:p<1) proves:

    exists a>0, Admissible p (density a) and Admissible p exponential and
      entropy p (convolution exponential exponential) - entropy p exponential
        < entropy p (convolution (density a) (density a)) - entropy p (density a)

It uses the inherited unconditional finite_tail_cutoff, with no residual analytic premises. SourceThresholdConsequence literally asserts existence of p0 in (0,1) such that for every p in (p0,1) and every admissible real density f, its increment is at most the baseline increment. not_source_threshold proves its negation by p=(p0+1)/2. No conditional SourceClaim is marked PASS.

## Verification and delivery

Lean 4.34.1 SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550; all eight package pins verified by reading immutable revision metadata, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. No git commands or package mutation.

Unchanged guard.py: serial j1, -M2700, warningAsError, autoImplicit=false, groupRSS2800MiB CPU210 wall230 nominal45ms sampling. Unchanged helper/replay guards: AS/groupRSS512MiB CPU210 wall230 nominal40ms sampling BLAS1. No cap raised; RSS sampling cannot exclude unsampled transients. Native bounded reads/apply_patch were authorized; script edits used helper_guard.

Development used oleans freshly compiled here from the inherited archive. Final archive contains no own compiled artifacts. FullAudit imports all eleven mathematical modules with import all to load actual bodies rather than exported stubs. It prints every actual type, checks environment origins against module constNames, collects transitive axioms and rejects unsafe/partial/axiom declarations, including generated helpers. Only propext, Classical.choice, Quot.sound are allowed. Inherited OriginAudit remains unchanged. Upstream .olean/.olean.private/.olean.server companions are hashed and their exact set cross-checked against the audit dependency list.

Deterministic source-only archive: component-source.zip. Fresh extracted replay (destination must not exist):

    python3 replay_guard.py python3 replay.py component-source.zip replay-fresh

Replay verifies manifests, frozen originals, compiler/packages/inputs and upstream companions; starts with zero own prebuilt artifacts; compiles all modules serially and runs exhaustive actual-body audit. replay-fresh/replay-receipt.json records all declaration types, origins, axioms, safety and resource receipts. FINAL-RECEIPT.json binds archive and receipt and final unchanged-original verification.

The first extracted replay stopped on an informational ring tactic message despite successful kernel compilation. Arithmetic normalization was changed to ring_nf; the failed extraction and first archive are retained as replay-first-failed and component-source-first.zip. No guard was weakened.

Failed probe/type/linter logs remain under logs/, with numbered failures for Deficit, Baseline and Endpoint. A rejected summary apply_patch made no changes. Some initial broad displays were truncated; no exhaustive conclusion relies on them. The inherited archive was separately freshly replayed successfully (51 declarations) before delivering these additions.
