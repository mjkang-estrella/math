from pathlib import Path
P=Path(__file__).resolve().parent
for name in ['screen-fisher.py','audit-fisher-full.py','fisher-full-screen.json','fisher-duplicate-screen.json','fisher-duplicate-hits.txt']:
 f=P/name;(P/('initial-'+name)).write_bytes(f.read_bytes())
 if f.suffix=='.py':f.write_text(f.read_text().replace(chr(92)*2+'.',chr(92)+'.'))
with (P/'failures.md').open('a') as f:f.write('\nExact-id regex in initial Fisher screens used a doubled raw-string backslash. Author and Fisher terms worked, but numeric ids were not reliably matched. Original scripts/results retained as initial-*; corrected supplemental screens rerun against the same frozen corpus. Original broad audit regex retained verbatim and its limitation superseded for exact ids by corrected Fisher audit.\n')
