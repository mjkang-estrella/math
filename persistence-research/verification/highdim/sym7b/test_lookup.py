import sys
sys.dont_write_bytecode=True
import importlib.util,json,pathlib
H=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from gen_sym import Generator
spec=importlib.util.spec_from_file_location('original_generator',H/'gen_sym_before_lookup.py');original=importlib.util.module_from_spec(spec);spec.loader.exec_module(original)
cases=pairs=0
for depth in range(1,7):
 for K in (8,89,1844,5408):
  t=(K&-K).bit_length()-1
  for pin2 in (False,True):
   p=max(depth,t+3)
   args=dict(coefs=(9,18),K=K,qmin=p,supply=[],pin2=pin2,pin_digits=depth)
   a=Generator(**args);b=original.Generator(**args)
   assert a.pin_periods==b.pin_periods and a.pin_pairs==b.pin_pairs
   pairs+=len(a.pin_pairs);cases+=1
out={'result':'PASS','cases':cases,'identical_ordered_pin_pairs':pairs,'change':'defaultdict index replaced by get(..., ()) on lookup only'}
(H/'lookup_controls.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
