from pathlib import Path
import subprocess
text=Path('manuscript/PAPER.txt').read_text()
pages=text.split('\f')
roff=['.po 0.8i','.ll 6.9i','.pl 11i','.ps 11','.vs 14p','.nf']
import textwrap
for i,page in enumerate(pages):
    if i: roff.append('.bp')
    roff.extend(['.sp 0.6i','.ft B',f'Shoe-pair discrepancy - {i+1}/{len(pages)}','.ft R','.sp 0.3i'])
    for paragraph in page.strip().split('\n\n'):
        lines=textwrap.wrap(paragraph.replace('\n',' '),width=92)
        roff.extend(('\\&'+l) for l in lines)
        roff.append('.sp 0.5')
    roff.append('.br')
source='\n'.join(roff)+'\n'
subprocess.run(['python3','-I','-B','write_lane.py','manuscript/paper.roff'],input=source,text=True,check=True)
ps=subprocess.run(['groff','-Tps','manuscript/paper.roff'],capture_output=True,check=True)
Path('output/pdf').mkdir(parents=True,exist_ok=True)
subprocess.run(['ps2pdf','-','output/pdf/shoe-discrepancy-completion.pdf'],input=ps.stdout,check=True)
print('PDF_GENERATED',len(pages),'planned pages')
