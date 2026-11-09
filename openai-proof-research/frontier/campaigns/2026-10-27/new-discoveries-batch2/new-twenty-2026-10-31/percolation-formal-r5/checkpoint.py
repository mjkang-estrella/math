from pathlib import Path
import json,sys,hashlib,re,shutil
R=Path(sys.argv[1]);P=R/'packet';S=P/'src';F=R/'fresh-extracted'
progress=json.loads((R/'normalized-progress.json').read_text());assert progress['replayed_steps']==13561
order=(P/'module-order.txt').read_text().splitlines();end=order.index('ReplayR5_0004')+1;order=order[:end]
U=R/'unreplayed-generated';U.mkdir(exist_ok=True)
for p in list(S.glob('*.lean')):
 if p.stem not in order:
  (U/p.name).write_bytes(p.read_bytes());p.unlink()
  if (F/'src'/p.name).exists():(F/'src'/p.name).unlink()
(U/'README.md').write_text('Generated drafts beyond addition 13,561 were not replayed. They are excluded from source-only.zip, module-order.txt and all claimed progress. The old target-17,500 endpoint and audit here are unverified drafts. Resume from normalized-progress.json, using the delivered generator as reference.\n')
# Both endpoint files here are new round-5 files. All inherited sources remain untouched.
(S/'EndpointR5.lean').write_text('''import ReplayR5_0004
namespace Percolation.NReplay
def RemainingSuffixUnsatR5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    (∀ c ∈ prefixR5_0004, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_normalized_after13561 (h : RemainingSuffixUnsatR5) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,prefix_soundR5_0004 v hv⟩
#print axioms not_conjecture20_normalized_after13561
end Percolation.NReplay
''');order.append('EndpointR5')
audit=(S/'AuditR4.lean').read_text().replace('import NormalizedEndpoint','import EndpointR5').replace('"AuditR4"','"AuditR5"')
audit=re.sub(r'  let localModules : Array String := #[^\n]+','  let localModules : Array String := #'+json.dumps(order+['AuditR5'],separators=(',',':')),audit)
(S/'AuditR5.lean').write_text(audit);order.append('AuditR5')
(P/'module-order.txt').write_text('\n'.join(order)+'\n')
front=(P/'replay-frontiers.tsv').read_text().splitlines();front=[line for line in front if line.split()[0] in order]
(P/'replay-frontiers.tsv').write_text('\n'.join(front)+'\n')
(P/'source-manifest.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(P))+'\n' for p in sorted(S.glob('*.lean'))))
manifest=json.loads((R/'inherited-source-comparison.json').read_text());assert all(hashlib.sha256((P/n).read_bytes()).hexdigest()==h for n,h in manifest.items())
shutil.copyfile(R/'replay.sh',P/'replay.sh');shutil.copyfile(R/'scan.py',P/'scan.py')
print({'modules':len(order),'progress':progress})
