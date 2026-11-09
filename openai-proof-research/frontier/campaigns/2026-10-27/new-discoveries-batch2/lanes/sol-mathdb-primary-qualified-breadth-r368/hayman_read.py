from pathlib import Path
R=Path(__file__).resolve().parent
ls=(R/'sources/hayman.txt').read_text().splitlines()
for label in ['4.23','6.75','6.104','7.35','7.52','8.6']:
 for i,s in enumerate(ls):
  if s.startswith('Problem '+label+' '):print('\nLINES',i+1,'to',i+50,'\n'+'\n'.join(ls[i:i+50]))
