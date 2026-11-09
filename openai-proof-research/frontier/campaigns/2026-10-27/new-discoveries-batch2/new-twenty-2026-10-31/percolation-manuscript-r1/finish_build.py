from pathlib import Path
import sys,json,shutil
D=Path(sys.argv[1]);vendor=D/'pdf-deps';vendor.mkdir(exist_ok=True)
shutil.copytree(D.parent/'rigid-cube-manuscript-r1/vendor/reportlab',vendor/'reportlab',ignore=shutil.ignore_patterns('__pycache__'),dirs_exist_ok=True)
fonts=D/'fonts';fonts.mkdir(exist_ok=True)
src=D.parent/'polynomial-manuscript-r1/pdf-deps/matplotlib/mpl-data/fonts/ttf'
for n in ['DejaVuSans.ttf','DejaVuSans-Bold.ttf']:shutil.copyfile(src/n,fonts/n)
p=D/'build_paper.py';s=p.read_text().replace('from xml.sax.saxutils import escape','sys.path.insert(0,str(Path(sys.argv[1]).resolve()/"pdf-deps"))\nfrom xml.sax.saxutils import escape').replace("'/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf'","str(D/'fonts/DejaVuSans.ttf')").replace("'/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf'","str(D/'fonts/DejaVuSans-Bold.ttf')")
s=s.replace("s=escape(s);", "s=escape(s).replace('&lt;br/&gt;','<br/>');")
p.write_text(s)
p=D/'paper.md';s=p.read_text();c=json.loads((D/'recomputation.json').read_text())['controls']
for line in s.splitlines():
 if line.startswith('| ') and any('| '+str(x['mask'])+' |' in line for x in c):
  x=next(x for x in c if '| '+str(x['mask'])+' |' in line)
  row=f"| {x['q']} | {x['r']} | {x['mask']} | {x['size']} | {', '.join(map(str,x['round_sizes']))} | {x['time']} |"
  s=s.replace(line,row)
p.write_text(s)
# certificate is external; only packet documentation retained, not duplicated trace data
for n in ['normalized-trimmed.json','normalized.cnf']:
 f=D/'evidence/percolation-formal-r8'/n
 if f.exists():f.unlink()
print('Local PDF dependencies prepared; control counts synchronized to verified output.')
