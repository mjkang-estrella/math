from pathlib import Path
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r1')
p=root/'src/Definitions.lean';s=p.read_text();s=s.replace('def rounds {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) : Nat → Infection q\n  | 0 => a\n  | n+1 => step P r (rounds P r a n)','def rounds {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) (n : Nat) : Infection q :=\n  Nat.rec a (fun _ state => step P r state) n');p.write_text(s)
