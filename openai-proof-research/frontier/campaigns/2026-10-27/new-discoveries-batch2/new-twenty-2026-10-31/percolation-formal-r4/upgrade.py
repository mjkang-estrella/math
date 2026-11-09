from pathlib import Path
r=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');p=r/'generate_replay.py';t=p.read_text();t=t.replace("data['steps'][N][0]","(data['steps'][N][0] if N<len(data['steps']) else 0)")
pos=t.index("mods+=['NormalizedEndpoint']")
t=t[:pos]+'''if N==len(data['steps']):
 assert rows[-1][1]==[]
 (S/'NormalizedEndpoint.lean').write_text(f\'''import {mods[-1]}
namespace Percolation
 theorem generatedNormalizedUnsat5_closed : GeneratedNormalizedUnsat5 := by
  rintro ⟨v,hv⟩
  have h := NReplay.der_{rows[-1][0]} v hv
  obtain ⟨z,hz,_⟩ := h
  cases hz
 theorem noMinimalTwoRound5_closed : NoMinimalTwoRound5 :=
  normalized_unsat_implies_noMinimal5 generatedNormalizedUnsat5_closed
 theorem not_conjecture20_unconditional : ¬ Conjecture20 :=
  not_conjecture20 noMinimalTwoRound5_closed
#print axioms generatedNormalizedUnsat5_closed
#print axioms noMinimalTwoRound5_closed
#print axioms not_conjecture20_unconditional
end Percolation
\''')
'''+t[pos:];p.write_text(t)
p=r/'package.py';t=p.read_text().replace("{data[min(j+500,N)][0]}","{data[min(j+500,N)][0] if min(j+500,N)<len(data) else 0}");p.write_text(t)
p=r/'packet/replay.sh';t=p.read_text().replace('sig=$(sha256sum src/*.lean | sha256sum | cut -d\' \' -f1)','sig=round4-rolling-v1').replace(' case "$m" in', ' sig=$(printf \'%s\\n%s\\n\' "$sig" "$(sha256sum "src/$m.lean" | cut -d\' \' -f1)" | sha256sum | cut -d\' \' -f1)\n case "$m" in');p.write_text(t)
