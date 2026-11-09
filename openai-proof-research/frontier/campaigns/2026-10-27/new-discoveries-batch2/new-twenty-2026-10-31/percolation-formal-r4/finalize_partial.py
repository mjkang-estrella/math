from pathlib import Path
import json,zipfile,hashlib
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');P=R/'packet';S=P/'src';F=R/'fresh-extracted';U=R/'unreplayed-generated/src';U.mkdir(parents=True,exist_ok=True)
order=(P/'module-order.txt').read_text().splitlines();keep=order[:434]+['NormalizedEndpoint','AuditR4']
assert order[433]=='NReplay023' and len(keep)==436
for p in list(S.glob('NReplay*.lean')):
 if int(p.stem[7:])>=24:
  (U/p.name).write_bytes(p.read_bytes());p.unlink()
(U/'NormalizedEndpoint-unverified-unconditional.lean').write_bytes((S/'NormalizedEndpoint.lean').read_bytes())
(R/'unreplayed-generated/README.md').write_text('These are generated but NOT fully replayed source drafts. NReplay024 failed the fixed CPU cap; no addition in that module or later is counted. The unconditional endpoint here is unverified and is excluded from source-only.zip. Continue from normalized-trimmed.json steps[12000], LRAT ID 35873.\n')
(S/'NormalizedEndpoint.lean').write_text('''import NReplay023
namespace Percolation.NReplay
-- Exactly the unreplayed normalized frontier refutation remains a hypothesis.
def NormalizedFrontierUnsat5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    (∀ c ∈ prefix023, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_normalized_after12000 (h : NormalizedFrontierUnsat5) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,prefix_sound023 v hv⟩
#print axioms not_conjecture20_normalized_after12000
end Percolation.NReplay
''')
p=S/'AuditR4.lean';t=p.read_text();start=t.index('  let localModules : Array String := #');end=t.index('\n  for (n, ci)',start);t=t[:start]+'  let localModules : Array String := #'+json.dumps(keep,separators=(',',':'))+t[end:];p.write_text(t)
assert set(keep)=={p.stem for p in S.glob('*.lean')}
(P/'module-order.txt').write_text('\n'.join(keep)+'\n')
(P/'replay-frontiers.tsv').write_text('\n'.join((P/'replay-frontiers.tsv').read_text().splitlines()[:24])+'\n')
(P/'source-manifest.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(P))+'\n' for p in sorted(S.glob('*.lean'))))
# Remove unverified modules from the extracted formal source tree, retaining their drafts above.
for p in F.joinpath('src').glob('NReplay*.lean'):
 if int(p.stem[7:])>=24:p.unlink()
with zipfile.ZipFile(R/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(S.glob('*.lean')):z.write(p,str(p.relative_to(P)))
 for n in ['module-order.txt','source-manifest.sha256','guard.sh','replay.sh','scan.py','replay-frontiers.tsv','normalized-trimmed.json','normalized.cnf','certificate-sha256.json','generator-correspondence.json','generate_replay.py']:z.write(P/n,n)
with zipfile.ZipFile(R/'source-only.zip') as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist());z.extractall(F)
progress=json.loads((F/'normalized-progress.json').read_text());assert progress['replayed_steps']==12000
(R/'normalized-progress.json').write_text(json.dumps(progress,indent=2))
print({'module_count':len(keep),'verified_additions':12000,'remaining_additions':117671,'next_lrat_id':35873,'source_sha256':hashlib.sha256((R/'source-only.zip').read_bytes()).hexdigest()})
