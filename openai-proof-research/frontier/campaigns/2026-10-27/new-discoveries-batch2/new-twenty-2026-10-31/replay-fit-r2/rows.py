from pathlib import Path
import re
L=Path(__file__).resolve().parent;S=L/'source'
mods=(L/'modules.txt').read_text().splitlines();out=[]
for m in mods:
 p=S/(m+'.lean');t=p.read_text()
 if not re.search(r'theorem [ACL]_(pq|qp|intertwine) :',t):out.append(m);continue
 head,body=t.split('namespace ActualSpectra330264\n',1)
 name=re.search(r'theorem (\w+) :',body)[1]
 rows=re.findall(r'  have r(\d+) : (.*) := by decide \+kernel',body)
 assert len(rows) in (18,19)
 rowmods=[]
 for start in range(0,len(rows),5):
  rm=m+'Rows'+str(start);rowmods.append(rm)
  rt=''.join('theorem '+name+'_r'+i+' : '+ty+' := by decide +kernel\n' for i,ty in rows[start:start+5])
  (S/(rm+'.lean')).write_text(head+'namespace ActualSpectra330264\n'+rt+'end ActualSpectra330264\n')
  out.append(rm)
 header=''.join('import '+rm+'\n' for rm in rowmods)+head
 stmt=body.split('\n')[0]
 proof='  ext i j\n  fin_cases i\n'+''.join('  · exact '+name+'_r'+i+' j\n' for i,_ in rows)
 p.write_text(header+'namespace ActualSpectra330264\n'+stmt+'\n'+proof+'end ActualSpectra330264\n')
 out.append(m)
(L/'modules.txt').write_text('\n'.join(out)+'\n')
