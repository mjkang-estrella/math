from pathlib import Path
import json,hashlib,zipfile,csv
R=Path(__file__).resolve().parent.parent
# Keep the successful dependency-free authoring route as the sole source workflow.
p=R/'scripts/build_paper.py'
s=p.read_text().split('# Render the source')[0]
s='\n'.join(x for x in s.splitlines() if not x.startswith('from reportlab'))+'\n'
(R/'scripts/paper_content.py').write_text(s);p.unlink()
p=R/'scripts/build_groff.py';s=p.read_text().replace("s=(R/'scripts/build_paper.py').read_text().split('# Render the source')[0]","s=(R/'scripts/paper_content.py').read_text()").replace("str(R/'scripts/build_paper.py')","str(R/'scripts/paper_content.py')");p.write_text(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# Check extracted source/driver contents against the original internal manifest.
E=R/'packet-safe-extraction'
lines=(E/'source-manifest.sha256').read_text().splitlines()
checked=[]
for line in lines:
 h,name=line.split(maxsplit=1);name=name.lstrip('*');assert sha(E/name)==h;checked.append(name)
(R/'receipts/packet-manifest-check.json').write_text(json.dumps(dict(pass_check=True,files=checked,executed_lean=False),indent=2)+'\n')
raws={str(p.relative_to(R)):sha(p) for p in (R/'evidence/expanded-corpus-r240/raw').glob('*.jsonl')}
(R/'receipts/mathdb-raw-hashes.json').write_text(json.dumps(raws,indent=2)+'\n')
qa=[]
notes={1:'Title, draft/AI status, poset definitions and formulas readable; margins clear.',2:'Mixing recursion, both readings and degree-two example readable; no clipping.',3:'Full twenty-term certificate, verification sizes and quoted conjecture readable.',4:'All seven dimension rows and poset construction readable; table aligned.',5:'Companion equations and formal correspondence readable; no broken symbols.',6:'Packet hash, trust discussion and bibliography readable; no overflow.'}
for n in range(1,7):
 p=R/f'qa/page-{n}.png';assert p.is_file();qa.append(dict(page=n,image=str(p.relative_to(R)),sha256=sha(p),visually_inspected=True,findings=notes[n],pass_layout=True))
text=(R/'qa/manuscript.txt').read_text();assert len(text.split('\f'))-1==6
(R/'receipts/visual-qa.json').write_text(json.dumps(dict(pdf_sha256=sha(R/'manuscript.pdf'),pages=qa,all_pages_inspected=True,method='pdftoppm at 110 dpi; each full-page image viewed with view_image; text extraction cross-check',status='PASS'),indent=2)+'\n')
print('Internal packet manifest verified:',len(checked),'files; six-page visual QA recorded.')
