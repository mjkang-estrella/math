from pathlib import Path
import subprocess
p=Path(__file__).resolve().parent
out=p/'output/pdf'; out.mkdir(parents=True,exist_ok=True)
parts=(p/'PAPER.txt').read_text().split('\n\n')
lines=['.po 0.8i','.ll 6.9i','.pl 11i','.de BP','.br','.bp','..','.wh 9i BP','.ps 10','.vs 13','.sp 0.2i','.ft B','.ps 16',parts[0].split('\n')[0],'.br','.ps 10','.ft R',parts[0].split('\n')[1],'.sp 0.3i']
for block in parts[1:]:
 if len(block)>2 and block[0].isdigit() and block[1]=='.':
  lines+=['.br','.ne 1i','.sp 1v','.ft B','.ps 12',block,'.br','.ps 10','.ft R','.sp 0.5v']
 else: lines+=['.sp 0.6v',block]
s='\n'.join(lines)+'\n'
subprocess.run(['python3','-I','-B',str(p/'write_lane.py'),'output/pdf/paper.roff'],input=s,text=True,check=True)
with (out/'paper.ps').open('wb') as f:
 subprocess.run(['groff','-Tps',str(out/'paper.roff')],stdout=f,check=True)
subprocess.run(['ps2pdf',str(out/'paper.ps'),str(out/'shoe-discrepancy-report.pdf')],check=True)
