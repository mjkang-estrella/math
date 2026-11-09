# Assemble final-receipt.json from guarded verifier outputs supplied in env-named files on stdin (JSON object of strings).
import json,sys
d=json.load(sys.stdin);d['integrity_pass_is_not_math_or_novelty_pass']=True
json.dump(d,open(sys.argv[1],'w'),indent=1);print('written',sys.argv[1])
