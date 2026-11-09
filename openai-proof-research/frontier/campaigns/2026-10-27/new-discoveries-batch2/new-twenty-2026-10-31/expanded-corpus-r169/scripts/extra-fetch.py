exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(__import__('pathlib').Path(__file__).parent/'fetch.py'),'exec'))
for ar in ['1610.04441','1708.04841','2407.15384']:
 fetch('https://arxiv.org/pdf/'+ar,ar+'.pdf')
