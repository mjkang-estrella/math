import pathlib
p=pathlib.Path(__file__).resolve().parent/'pebbling.py'
s=p.read_text().replace('range(2,6)','range(5,7)').replace('if n==5:','if n>=5:').replace('if mask%7:continue','if n==6 and mask%97:continue').replace('pebbling-search.json','pebbling-extended.json').replace('all connected labeled simple graphs n2..4; n5 diameter<=2 with edge mask divisible by7','all connected labeled simple graphs n5 diameter<=2; n6 diameter<=2 with edge mask divisible by97')
exec(compile(s,str(p),'exec'))
