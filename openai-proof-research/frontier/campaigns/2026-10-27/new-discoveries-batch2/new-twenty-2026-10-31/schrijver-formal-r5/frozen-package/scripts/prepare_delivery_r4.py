from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent.parent
old=json.loads((r/'frozen-before.json').read_text());now={m:hashlib.sha256((r/'src'/m).read_bytes()).hexdigest() for m in old};assert old==now
(r/'frozen-after.json').write_text(json.dumps(now,indent=2))
sources={p.stem:p for p in (r/'src').glob('*.lean')};order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for i in re.findall(r'^import (\w+)',sources[m].read_text(),re.M):
  if i in sources:visit(i)
 order.append(m)
for m in sorted(sources):visit(m)
(r/'outputs/modules.json').write_text(json.dumps(order,indent=2))
(r/'SUMMARY.md').write_text('''# MathDB 352827 round 4 partial handback

Incomplete; not accepted. The unconditional theorem mathdb_352827 is absent. Root decides.

RotationCheck.lean proves soundness of a finite bit comparison checker using rotateMask_bit. The 100 Rotation28 modules kernel-check explicit rotation and representative witnesses for every stored index. RotationCoverage28.lean proves indexed_rotation_coverage28 and rotation_coverage28_from_enumeration. The new endpoint mathdb_352827_round4_conditional requires exactly Enumeration27 and Enumeration28; rotation coverage is derived from Enumeration28.

GapRankInverse.lean proves that subtracting the rank from a sequence with gaps at least two gives a strictly increasing sequence bounded by n-k+1, and proves exact reconstruction by adding the rank. These lemmas are not yet connected to the sorted list of an arbitrary literal stable subset. They do not establish enumeration completeness.

Remaining exact Props are the frozen definitions Enumeration27 and Enumeration28 in BridgeTransport.lean. No cardinality argument substitutes for equality. RotationRepresentativeCoverage28 is proved conditionally on Enumeration28, not unconditionally. The gap enumeration completeness and its equality with each stored table remain undone.

Next round: construct the increasing enumeration of a literal stable Finset, prove the consecutive gap bounds from Stable, apply subtractRank_inverse / subtractRank_strict / subtractRank_bound, prove membership in an executable combination enumerator, and kernel-check equality with each stored table. Apply mathdb_352827_round4_conditional to the two resulting enumeration theorems.

All 362 frozen source modules remain byte-identical. frozen-before.json and frozen-after.json record their hashes. Audits check declaration flags, generated companions, attributes and transitive axioms, plus exact equality of the audited module set with the conditional endpoint import closure. Fresh extraction, strict serial builds, leanchecker, negative controls and their resource receipts are reported in results.json. No child agents, git, shared ledger edits, external messages, uploads, network requests or browser tabs were used. Writes were lane-local. Extracting the input archive initially overwrote the lane TASK.txt with the archived round-3 task; it was restored from the binding round-4 text read before extraction. The archived task is preserved in inputs/round3-TASK.txt. Failed development logs are retained.
''')
for name,text in [('PROOF.md','''

## Round 4 additions and limits

For each stored mask a, the new certificate supplies a shift t and an upper-tree root r. The checker tests t<28 and r<3185, finds r in upperRoots28, and compares all 28 bits a[i] with maskAt28(r)[(i+t) mod 28]. rotationBitsCheck_sound uses rotateMask_bit and the high-bit bounds to prove equality of masks. decode_rotateMask then proves equality of literal rotated vertices. All 3,185 witnesses are kernel-checked in 100 chunks. This proof requires no reflection or unproved automorphism.

Under Enumeration28, literalIso28 is surjective, so every literal vertex inherits its stored-index rotation witness. Thus the round-3 endpoint's rotation hypothesis is eliminated; both enumeration hypotheses remain. This is not an unconditional refutation.

For a sorted sequence a with a(i)+2≤a(i+1), induction gives a(i)+2(j-i)≤a(j). Hence i≤a(i), the natural subtraction a(i)-i is exact, is strictly increasing and is less than n-k+1 when the original k entries are less than n. GapRankInverse formalizes these arithmetic facts. The stable-subset-to-sequence and enumeration-equality bridges remain open.
'''),('STATEMENT-CORRESPONDENCE.md','''

## Round 4 correspondence

The definitions and conventions in the frozen modules are unchanged. rotationBitsCheck compares the bit at i of a with the bit at (i+t) mod n of b, matching rotateSet's addition by t. rotateMask_bit supplies the exact correspondence and rotationBitsCheck_vertex converts mask equality to subtype equality. rotation_coverage28_from_enumeration has the explicit hypothesis Enumeration28. mathdb_352827_round4_conditional has exactly Enumeration27 and Enumeration28 as residual hypotheses. No theorem with the unconditional required name is provided.
'''),('REPRODUCE.md','''

## Round 4 replay

Use the delivered archive schrijver-partial-source.zip, extract into an empty lane-local directory, and run `python3 -I scripts/replay.py --resume`. The source manifest fixes every source, script and prose document. outputs/modules.json lists all modules in dependency order. The runner uses the pinned Lean 4.34.1 and read-only mathlib cache, -j1 -M3500 -DwarningAsError=true, unique logs and per-process resource caps. It runs leanchecker on every module and rejects all negative controls. Resource receipts and replay-result.json give actual outcomes. New audits are ClosureAuditRound4.lean and AuditRound4.lean; frozen audits remain untouched. Root decides acceptance.
''')]:
 p=r/name;p.write_text(p.read_text()+text)
print(len(order),'modules')
