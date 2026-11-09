from pathlib import Path
p=Path('Definitions.lean');s=p.read_text();start=s.index('def allWords :');end=s.index('\ntheorem mem_allWords',start)
s=s[:start]+'''def allWords (n m : ℕ) : List (List ℕ) :=
  Nat.rec [[]] (fun _ ws => (List.range m).flatMap fun a => ws.map ((a+1) :: ·)) n
'''+s[end:];p.write_text(s)
