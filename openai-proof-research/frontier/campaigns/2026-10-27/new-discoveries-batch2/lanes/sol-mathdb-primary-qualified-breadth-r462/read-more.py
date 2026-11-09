import pathlib,re
L=pathlib.Path(__file__).resolve().parent
for f in sorted((L/'sources').glob('*.txt')):
 if f.stem.isdigit() and int(f.stem) not in [323232,323303,323347,323487,323515,323550,323626,323627,323639,323660,323693,323759,323809,323829,323850,324031,324305,324316,324344,324390,324431,324452]:continue
 s=f.read_text();ms=list(re.finditer(r'Conjecture\s+(?:\d|[A-Z])',s));ms=ms[-2:]
 if not ms:ms=list(re.finditer('conjecture',s))[-2:]
 print('\nFILE',f.stem)
 for m in ms:print('OFFSET',m.start(),s[max(0,m.start()-100):m.start()+950])
