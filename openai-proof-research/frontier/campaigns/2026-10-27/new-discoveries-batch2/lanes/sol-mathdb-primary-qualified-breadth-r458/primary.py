from pathlib import Path
import re,json,sys
L=Path(__file__).parent
spec='''0709.4387|Conjecture 2 For
0712.1357|Conjecture 1[.]
0803.0538|Conjecture[.] For
0804.1289|Conjecture 3[.]
0804.1299|Conjecture 2 For
0804.1307|Conjecture 1[.]
0804.3825|Conjecture 1:
0804.4145|Conjecture 12[.]
0806.1772|Conjecture 2.12
0806.2264|Conjecture 3 All
0806.2421|Conjecture 12 For
0806.3243|Conjecture 3.2:
0807.4846|Conjecture 1:
0808.3760|Conjecture 5.1
0809.4627|Conjecture 13[.]
0810.1735|Conjecture 2:
0811.2249|Conjecture 1 Let
0812.3082|Conjecture 5.2
0812.5038|Conjecture 3.2[.]
0901.3945|Theorem 2.9[.] Let
0903.0198|Conjecture 1 Let
0903.3048|Conjecture 1 [(]
0903.5142|Conjecture 5[.]
0904.1481|Conjecture 3.1[.]
0905.0135|Conjecture[.] There is a finite
0905.3820|Conjecture 1.1[.]
0905.3949|Conjecture 3.1 For
0906.3993|Conjecture 1 For
0907.1186|Conjecture 2.20
0907.1583|Conjecture 1.2 [(]
0908.1981|Conjecture 7.9
0908.3895|Conjecture 4 [(]
0909.0086|Conjecture 4.4[.]
0909.2468|Conjecture 1.1 [(]
0910.0749|Conjecture 1[.] Let
0910.2445|Conjecture 7.1[.]
0910.2469|Conjecture 4.2 For
0911.4008|Conjecture 1[.] Let
0912.1150|Conjecture 8[.]
1001.3628|Conjecture 5.1[.]
1002.0190|Conjecture 9 [(]
1002.2115|Conjecture 3.2[.]
1003.0021|Conjecture 5[.]
1003.4422|Conjecture 1[.]
1003.5002|Conjecture 3.2 [(]
1003.5632|Theorem 1.4[.]
1004.1917|Conjecture 13[.]
1004.2435|Conjecture[.] If'''
out=[]
for i,line in enumerate(spec.splitlines()):
 aid,pat=line.split('|');p=L/'sources'/f'{aid}.txt';lines=p.read_text().split('\n');hits=[j for j,s in enumerate(lines) if re.search(pat,s)];assert hits,(aid,pat)
 n=hits[0];a=max(0,n-3);b=min(len(lines),n+12)
 passage='\n'.join(f'{k+1}: {lines[k]}' for k in range(a,b))
 out.append({'source':aid,'path':str(p.resolve()),'start_line':a+1,'end_line':b,'passage':passage,'scope':'read selected question/result passage only; no whole body or dependency audit'})
 if int(sys.argv[1])<=i<int(sys.argv[2]):print('\nSOURCE',aid,'\n'+passage)
(L/'read-primary-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
