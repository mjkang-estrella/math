import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent
anchors={'1004.3081':['Conjecture 4.7. There'],'1004.3332':['Conjecture 1: For'],'1004.5571':['Conjecture 1:'],'1005.3133':['Conjecture 8.1.'],'1005.5186':['Theorem 2.17.'],'1006.2416':['Conjecture 2.3.17'],'1008.4707':['Conjecture 2 ('],'1009.0792':['Conjecture 6.3.'],'1009.6019':['Conjecture 1.3.'],'1010.0745':['Conjecture 3.5.'],'1010.5042':['Conjecture 1. —'],'1010.5167':['Conjecture 7 ('],'1010.5442':['Conjecture 1. For','Conjecture 2. For'],'1011.4476':['Conjecture 2. Suppose','Conjecture 5. Suppose'],'1011.5930':['Conjecture 2.4.'],'1012.1231':['Conjecture 1. If'],'1101.3135':['Conjecture 3.'],'1101.5747':['Conjecture 2.13'],'1102.1611':['Conjecture 29.'],'1102.2631':['Conjecture 6.5'],'1102.4979':['Conjecture 6.'],'1102.5438':['Conjecture'],'1103.1691':['Conjecture 2.4'],'1103.3858':['Conjecture'],'1103.3917':['conjecture'],'1103.5010':['Conjecture 7.2.3.'],'1104.3528':['conjecture'],'1104.3602':['four-atom','four atom','Four-atom'],'1104.4367':['Treglown'],'1105.0796':['Proposition 4.1.'],'1105.1764':['Conjecture 9.1.','Conjecture 9.3.'],'1106.0369':['interesting','Wójcik','Wojcik'],'1106.0631':['Conjecture 5.'],'1106.1625':['Conjecture 15.'],'1106.3755':['Theorem 8 For'],'1106.4065':['Conjecture 2.'],'1106.4235':['Conjecture 8.3.'],'1106.6144':['Conjecture 4.8','Conjecture 6.6'],'1107.0207':['Conjecture 3.'],'1107.1130':['Conjecture 3.','Conjecture 4.'],'1107.1219':['Conjecture 1.2'],'1107.2630':['Conjecture 2.1.'],'1107.2888':['Conjecture 1 inf'],'1108.3444':['Conjecture 4.9'],'1108.4902':['Conjecture 10 (']}
meta=[];o=(L/'target-passages.txt').open('w')
for key,patterns in anchors.items():
 lines=(L/'sources'/(key+'.txt')).read_text().splitlines();spans=[]
 for pat in patterns:
  hits=[i for i,s in enumerate(lines) if pat.lower() in s.lower()]
  if hits:
   i=hits[-1] if key in ['1103.3858','1103.3917','1104.3528','1106.0369'] else hits[0]; a=max(0,i-5);b=min(len(lines),i+24);spans.append([a+1,b]);o.write('\n=== '+key+' ===\n'+'\n'.join(f'{j+1}: {lines[j]}' for j in range(a,b))+'\n')
  else:o.write('\nMISSING ANCHOR '+key+' '+pat+'\n')
 meta.append({'key':key,'ranges':spans,'line_convention':'Python str.splitlines, including form-feed page breaks'})
(L/'read-passages.json').write_text(json.dumps(meta,indent=2)+'\n')
