#!/usr/bin/env python3
"""One-time seal of this review's own exact selected packet only."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,stat
ROOT=Path(__file__).resolve().parent
REL='frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/structural-r233-proof-r1'
OUTSIDE={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-CHECK.json'}
PAYLOAD='''READING-LIMITS.md REVIEW.md artifact-controls.json author-baseline.json check_author.py controls/copy/copy.txt controls/original.txt guards.json original-post-read.json primary-boundary-classification.json primary-mask-resolutions.json read_admitted.py run_controls.py semantic-reads.jsonl source-binding.json verify_packet.py working-analysis.md seal_once.py selection.json'''.split()
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write_new(name,obj):
    b=(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode() if not isinstance(obj,str) else obj.encode()
    with (ROOT/name).open('xb') as f:f.write(b)
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
assert not any((ROOT/n).exists() for n in OUTSIDE|{'selection.json'})
v=module('review_verifier',ROOT/'verify_packet.py');c=module('author_checker',ROOT/'check_author.py')
assert v.surface(ROOT)==set(PAYLOAD)-{'selection.json'}
selection={'schema':'structural233-proof-r1-exact-selection-v1','root':REL,'paths':sorted(PAYLOAD)}
write_new('selection.json',selection)
entries=[]
for name in sorted(PAYLOAD):
    p=ROOT/name;p.chmod(0o444)
    if name=='REVIEW.md':kind='reviewer original mathematical reasoning; local research only'
    elif name.endswith('.py'):kind='reviewer local artifact/access code; no mathematical certification'
    elif name.startswith('controls/'):kind='tiny reviewer-owned copied artifact control'
    else:kind='private/local reading, access, baseline or working metadata; preserve original rights where applicable'
    entries.append({'path':name,'bytes':p.stat().st_size,'mode':'0444','sha256':digest(p),'classification':kind})
manifest={'schema':'structural233-proof-r1-manifest-v1','root':REL,'sealed_once_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'selection_sha256':digest(ROOT/'selection.json'),'entries':entries,'detached_outside_manifest':sorted(OUTSIDE),'rights':'All artifacts local only; protected source/primary bodies are not copied here; named metadata remain private/local under original rights. No publication authorized.','mathematical_verdict_location':'REVIEW.md; proposed for parent adoption only; artifact checks are not mathematical gates'}
write_new('MANIFEST.json',manifest);(ROOT/'MANIFEST.json').chmod(0o444)
mh=digest(ROOT/'MANIFEST.json');sd=digest(ROOT/'selection.json');rh=digest(ROOT/'REVIEW.md')
final=f'''# Structural233 correctness review r1 — FINAL

Proposed verdict for parent adoption: **PASS**, at the complete unchanged frozen statement and submitted proof, relative to the stipulated truth of Source357 and all operative upstream proofs. No essential repair, added hypothesis, narrowing, replacement theorem or unresolved correctness obligation was identified. No contribution verdict, acceptance or count is assigned.

REVIEW.md contains the complete independent reasoning for all thirteen requested checks, exact source interfaces, objections and resolutions, strongest relevant alternatives and auxiliary assertions. READING-LIMITS.md separately records actual independent reads, authentication, exclusions and limitations. REPORT.md is the detached outside report, within the exclusive review root and outside the selected manifest.

review_sha256={rh}
manifest_sha256={mh}
selection_sha256={sd}

Reviewed author statement SHA256: 3d9a20ab3e17778919f3ae159b1e297d682c63b4a8c98474fb9c99d7e7fe65da
Reviewed author proof SHA256: 302d436f1beb448f9c06031d6a078892a433099d5b845b84d4b76b351659d286

The admitted author originals are read-only and baseline checked. No peer review, contribution review, parent assessment, foreign task/status body, git operation, shared edit, nested agent, public action, browser UI or downstream formal/manuscript/release action occurred. The exact source truth was stipulated, not audited. No formal certification or history/literature completeness is claimed.

This is the reviewer's own exact selected packet, sealed once. Its read-only verifier requires explicit detached FINAL/MANIFEST/REPORT hashes and verifies selected bytes, modes and the complete surface. Tiny copied controls concern artifact integrity only. Protected bodies and named metadata remain private/local under original rights.
'''
write_new('FINAL.md',final);(ROOT/'FINAL.md').chmod(0o444);fh=digest(ROOT/'FINAL.md')
report=f'''# Structural233 proof review r1 — outside REPORT

**Proposed correctness verdict: PASS, for parent adoption only.** The entire unchanged frozen theorem and submitted proof are supported relative to stipulated Source357 truth, without an essential repair, added hypothesis, narrowing, replacement or unresolved correctness obligation. No contribution verdict, acceptance or count is assigned.

The full reasoning is REVIEW.md, SHA256 {rh}. It checks the exact full noncollapsed RCD category and Hausdorff normalization; all-pole matrix heat identity and cutoff/curvature residual; Gaussian envelopes and noncommuting accumulation; uniform localization tails and fine-pole interpolation; fine nets and all derivative supports; the auxiliary weight-one source interface; equation (1.1) and its cross terms; fixed near-minimizing centers and every field/jet bound; old-level inverse iteration and square-summed metric errors; uniform chart tails and segment containment; every ambient pair, open image and arbitrary eta; exact rescaling and the round-sphere escape example. Concrete objections are resolved there. The expansions made in the review unpack the submitted argument and exact source interfaces; none changes its scope.

READING-LIMITS.md records complete operative source reading and narrower independent primary comparison, with no claim to inherited author reading, external-dependency closure, literature or history clearance. One incidental source-driver PDF author metadata line was exposed and recorded. No semantic output truncation occurred. No original-history, peer review, parent assessment or foreign-owner status/activity body was admitted. Source truth was not audited. No formal support or build is claimed.

All 48 author manifest entries plus the five authorized detached originals were independently authenticated against the supplied anchors and a preserved 53-file byte/mode baseline. The eight canonical source blobs were independently bound to the exact complete pinned tree; eight primary container/TeX identities were also checked. These checks are not mathematical proof. Final original rechecks are recorded in original-post-read.json and SEAL-CHECK.json.

The exclusive writable root is {REL}/. Every command used the actual project root. No shared edit, git operation, nested agent, browser UI, publication, upload, submission, contact, downstream formalization, manuscript or release occurred. Protected source/primary bodies remain in their admitted originals; named metadata remain private/local under original rights.

The reviewer's own selected packet was sealed once, with explicit detached anchors:
FINAL.md SHA256: {fh}
MANIFEST.json SHA256: {mh}
The SHA256 of this REPORT.md is computed directly from its completed bytes and recorded in ANCHORS.json and the handoff. verify_packet.py is read-only and requires all three explicit anchors. Six tiny copied artifact controls tested valid bytes/surface and rejection of byte, mode, selection and extra-file changes, preserving the 25-byte original. Artifact success is not a correctness gate.

Authorized provenance: Codex / GPT-6 Astra / xhigh / default, as supplied. Parent alone adopts verdicts and integrates.
'''
write_new('REPORT.md',report);(ROOT/'REPORT.md').chmod(0o444)
anchors={'FINAL.md':fh,'MANIFEST.json':mh,'REPORT.md':digest(ROOT/'REPORT.md')}
write_new('ANCHORS.json',anchors);(ROOT/'ANCHORS.json').chmod(0o444)
# Actual checks before the last detached record is created; final complete check follows.
v.verify_payload(ROOT,entries,selection['paths'])
v.verify_surface(ROOT,selection['paths'],OUTSIDE-{'SEAL-CHECK.json'})
original_check=c.check()
write_new('SEAL-CHECK.json',{'selected_payload_and_modes_verified':True,'surface_before_this_detached_record_verified':True,'author_originals':original_check,'detached_anchors':anchors,'read_only_verifier':'verify_packet.py','mathematical_gate':False})
(ROOT/'SEAL-CHECK.json').chmod(0o444)
result=v.verify(ROOT,anchors)
# Recheck originals after the completed own packet check; no writes to any original.
assert c.check()==original_check
print(json.dumps({'review_sha256':rh,'review_bytes':(ROOT/'REVIEW.md').stat().st_size,'complete_packet_check':result,'author_originals_after_final_checks':original_check},indent=2,sort_keys=True))
