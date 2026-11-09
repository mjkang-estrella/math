from pathlib import Path
r=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');p=r/'generate_replay.py';t=p.read_text()
t=t.replace("if k==0:term='input_nonfull v hb'", "if k==0:term='input_nonfull v hb';cc='pts5.map (fun p => (SatVar.x p, true))'")
t=t.replace("elif k<=31:term=f'input_omit {k-1} v hb'", "elif k<=31:term=f'input_omit {k-1} v hb';cc=f'omitClause5 {k-1}'")
t=t.replace("term=f'input_contain {a} {p} (by decide) v hb'", "term=f'input_contain {a} {p} (by decide) v hb';cc=f'containClause5 {a} {p}'")
a="out += [f'  exact holds_decode v cl_{i} (by simpa only [cl_{i}, decodeClause, decodeVar, omitClause5, containClause5, pts5, List.map_cons, List.map_nil] using ({term}))']"
b="out += [f'  apply holds_decode',f'  have he : decodeClause cl_{i} = ({cc}) := by decide','  rw [he]',f'  exact {term}']"
assert a in t;t=t.replace(a,b);p.write_text(t)
p=r/'package.py';t=p.read_text().replace('import Lean\nopen Lean','import Lean\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nopen Lean');p.write_text(t)
