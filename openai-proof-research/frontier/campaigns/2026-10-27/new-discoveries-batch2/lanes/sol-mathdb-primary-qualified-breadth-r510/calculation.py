# Recompute only the arithmetic in the PUBLIC Pate certificate; no novelty claim.
import json,pathlib
out={'source':'arXiv:2101.03428v5 Section 4','gram_permanent':120+16*24,'tensor_norm_squared':2**9*12+2**11*2+2**9*4,'coefficient_norm_squared':4*2+4*4}
out['rayleigh_quotient']=out['tensor_norm_squared']//out['coefficient_norm_squared'];assert out['tensor_norm_squared']==512*24 and out['rayleigh_quotient']>out['gram_permanent']
out['scope']='Executed exact integer arithmetic only; tensor identity and Gram/permanent dependencies read selectively, not independently replayed. Public certificate; no new result.'
pathlib.Path(__file__).with_name('calculation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
