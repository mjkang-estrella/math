from pathlib import Path
import json,re,hashlib,sys
L=Path(__file__).parent
selected={'0709.4387':88,'0712.1357':90,'0803.0538':202,'0804.1289':1150,'0804.1299':459,'0804.1307':90,'0804.3825':207,'0804.4145':265,'0806.1772':196,'0806.2264':273,'0806.2421':679,'0806.3243':851,'0807.4846':212,'0808.3760':707,'0809.4627':1018,'0901.3945':209,'0907.1186':661,'0907.1583':83,'0908.1981':1086,'1002.2115':242,'1003.0021':290,'1003.4422':270,'1003.5002':544,'1003.5632':113,'1004.1917':575,'1004.2435':175}
selected.update({'0812.3082':625,'0812.5038':494,'0903.0198':676,'0903.3048':48,'0903.5142':611,'0904.1481':471,'0905.0135':1179,'0905.3820':152,'0905.3949':971,'0906.3993':521,'0909.0086':878,'0909.2468':36,'0910.0749':270,'0910.2445':745,'0910.2469':600,'0911.4008':142,'0912.1150':150,'1001.3628':1540,'1002.0190':199})
# For remaining sources take their last numbered conjecture before bibliography, only as triage reading.
rows=[]
for i,p in enumerate(sorted((L/'sources').glob('*.txt'))):
 lines=p.read_text().split('\n');hits=[j+1 for j,l in enumerate(lines) if re.match(r'^\s*Conjecture\s+[0-9]',l)]
 n=selected.get(p.stem,hits[-1] if hits else 1);a=max(1,n-8);b=min(len(lines),n+20)
 passage='\n'.join(f'{k}: {lines[k-1]}' for k in range(a,b+1))
 row={'source':p.stem,'path':str(p.resolve()),'start_line':a,'end_line':b,'passage':passage,'scope':'selected primary passage only; not whole body/dependency audit'};rows.append(row)
 if int(sys.argv[1])<=i<int(sys.argv[2]):print('\nSOURCE',p.stem,'\n'+passage)
(L/'primary-passages.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
