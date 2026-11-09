from pathlib import Path
import re
L=Path(__file__).resolve().parent
rows=[]
for p in sorted((L/'logs').glob('*.log')):
 text=p.read_text(errors='replace')
 m=re.findall(r'GUARD peak_kib=(\d+) elapsed=(\d+) status=(\d+) reason=(\w*)',text)
 if m:
  rss,wall,status,reason=m[-1];rows.append((p.name,wall,rss,status,reason or 'none'))
(L/'timings.tsv').write_text('log\twall_s\tpeak_rss_kib\twait_status\treason\n'+''.join('\t'.join(r)+'\n' for r in rows))
(L/'TIMINGS.md').write_text('| Log | Wall s | Peak RSS KiB | Raw wait status | Reason |\n|---|---:|---:|---:|---|\n'+''.join('| '+' | '.join(r)+' |\n' for r in rows))
