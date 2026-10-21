"""One-time seal of this exclusive root. Do not rerun or refresh a sealed packet."""
from pathlib import Path
import sys,json,subprocess
R=Path(__file__).resolve().parents[1];sys.path.insert(0,str(R))
from verify import inventory,digest,verify,OUTSIDE
assert not any((R/n).exists() for n in OUTSIDE), 'already sealed; no reseal'
final='''# Analytic r140 final handoff

PREFREEZE / no nominee. No statement frozen, no independent correctness/contribution grade, acceptance, count or downstream stage. Authorized Codex / GPT-6 Astra / high / default service tier. Campaign remains the supplied 19/20 context, latest R041; parent alone integrates/counts.

The sustained family is Source080 endpoint Schrödinger evolution under potentials. Source079 local smoothing received catalogue navigation only. The strongest compatible reduction closes real time-independent bounded potentials at exact s=n/[2(n+1)] by spectral temporal regularity, one equation-controlled modulation derivative and Bourgain transfer. Existing corrected wave-operator structure formulas also transfer the source estimate at their actual potential-class hypotheses. The later-read r45 weighted-tree output improvement transfers too; it is not another nominee.

The remaining operation is exact-endpoint common-time-graph control for general small real L^{n/2} potentials, concrete in R³ at H^{3/8}. Form realization/persistence and endpoint Strichartz absorption are paid. No compatible solution-specific retarded maximal estimate closes the remaining interface. The concentrated-potential calculation gives an explicit N^{2b-1} obstruction to a uniform X^{s,b}->X^{s,b-1} potential multiplication bound for b>1/2. It does not disprove the evolution estimate or other methods.

DERIVATION.md retains the integrated mathematics and all qualifications. GAPS.md states the unpaid operation without a renamed conjecture or supporting substitute. READING-LIMITS.md discloses actual source/primary/history extents, failures, late reads, truncated displays, coarse omissions and false admissions. No priority, exhaustion or perfect-isolation certificate. All old scopes remain immutable.

The arithmetic-r112 isolation addition was applied in this same original turn after synthetic controls and before sealing, with no subsequent broad scan. ISOLATION-STEER.json preserves timing and script hashes; older scan records retain their actual filters.

The packet is sealed once with exact payload membership and three outside envelopes (this FINAL, REPORT and MANIFEST), all inside the authorized root. External detached SHA256 anchors are handed off in the thread. Artifact integrity is not a mathematical gate. Protected inputs remain private/local under original rights.
'''
report='''# Outside report for analytic r140

Outcome: PREFREEZE / no nominee. Full author-proof nomination and all independent mathematical gates remain absent. No old target was weakened, changed, exhausted or regraded.

Research evidence: the bounded-potential endpoint transfer is completely accounted for by compatible standard operations. The critical-potential attempt also credits corrected Beceanu--Schlag structure and Keel--Tao retarded endpoint absorption; its remaining maximal-interface gap is not inferred from a single failed route. A concrete scaled thin-shell test rules out only the uniform b>1/2 Bourgain multiplication estimate.

Authentication: 33 canonical Source080 text blobs match sizes/Git blobs from the complete stipulated13223-entry tree, with independent SHA256. Primary raw archives and selected extracted members have separate identities; Choi v3, Beceanu--Schlag1612 v3 and1701 v1 were read at documented extents. The guessed1701 v2 returned404;1612 single-TeX gzip was recovered after tar rejection. Author-hosted Keel--Tao PDF bytes, extraction and one rendered page are retained. No latest-version or full-transitive-literature certificate.

Original authentication is distinct from copy membership. Named original observations and selected-copy inventories are separate, with I66 retained only as the selected1-100 excerpt. Neither an incoming manifest nor an original whole-root claim certifies a reduced copy. Required r139 completed exceptions are included with their original rights.

Material isolation limits: an initial outer-project filename traversal preceded pruning; no resulting discovered body was selected. Subsequent scanners enforced named active-peer exclusions but imperfect derivative-role filters admitted private/copy/vendor/role aliases; later scripts prospectively improved them. Full details, counts, late-read and truncation recovery limits are in READING-LIMITS and ISOLATION. No peer body/activity inference supplies a premise. Same-turn r112 exclusion added2026-10-21T02:11:24.927761+00:00 before seal; no later broad research scan.

Six small synthetic copied controls: clean/restored accepted; changed payload, missing payload, extra hidden file and wrong external anchor rejected. Every verifier invocation left its fixture byte inventory unchanged. Controls have their own inventories; no original packet was modified or resealed. verify.py reads only, requires three external anchors and checks exact membership, SHA256, canonical-source Git-blob metadata, selected-copy hashes and raw-to-extracted primary bindings. No mathematical conclusion is tested by these controls.

All intentional writes stayed within the exclusive r140 root. No git/staging/commit, nested agent, browser UI, installation, publication/upload/submission/contact, or downstream formal/manuscript/release work. This is not an OS-wide unchanged-files certificate. Parent alone integrates, reviews and counts.
'''
(R/'FINAL.md').write_text(final);(R/'REPORT.md').write_text(report)
files,dirs=inventory(R)
m={'schema':'r140.exact-payload.v1','outside':sorted(OUTSIDE),'files':{k:v for k,v in sorted(files.items()) if k not in OUTSIDE},'directories':dirs}
(R/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
anchors={n:digest((R/n).read_bytes()) for n in sorted(OUTSIDE)}
before=inventory(R);result=verify(R,anchors);assert before==inventory(R),'verifier changed original packet'
cli=subprocess.run(['sha256sum',*[str(R/n) for n in sorted(OUTSIDE)]],capture_output=True,text=True,check=True).stdout
for line,n in zip(cli.splitlines(),sorted(OUTSIDE)):assert line.split()[0]==anchors[n]
print(json.dumps({'anchors':anchors,'verification':result,'read_only_replay':True,'independent_hash_check':'hashlib and sha256sum agree'},indent=2));print(cli)
