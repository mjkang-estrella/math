import json,pathlib,sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from gen_sym import Generator
G=Generator([9,9,9,9,54],2303,3)
print('decimal periods',G.pin_periods,'representatives',len(G.pin_pairs))
for p in (11,13,37,41,271,10838689,999999000001):
    e=next((e for ee in G.byperiod.values() for e in ee if e[0]==p))
    G.forbidden(1,e,(2,None),(0,None))
    h,images,inv=G.cosets[(p,None,None)]
    print(p,'period10',e[1],'old_index',(p-1)//e[4], 'new_cosets',len(images),'h',h,'new_index',(p-1)/(h*len(images)) if images else 'empty')
