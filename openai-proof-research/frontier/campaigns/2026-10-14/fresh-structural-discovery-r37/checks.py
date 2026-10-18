# Author: Myeongjin Kang (no affiliation). SPDX-License-Identifier: MIT
"""Read-only finite replay of new and selected historical diagnostics."""
import importlib.util,json,runpy
from pathlib import Path
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('new_interfaces',P/'check-new-interfaces.py')
new=importlib.util.module_from_spec(spec);spec.loader.exec_module(new)
result=new.run()
assert result==json.loads((P/'new-interface-checks.json').read_text())
old=runpy.run_path(str(P/'explore.py'))
profile=json.loads((P/'minimal-profile-certificate.json').read_text())
actual=old['layers'](profile['inputs'],profile['seed'])
assert json.loads(json.dumps(actual))==profile
exact=runpy.run_path(str(P/'search-budget.py'))['exact']
certificate=json.loads((P/'period-budget-counterexample.json').read_text())
actual=json.loads(json.dumps(exact(certificate['inputs'])))
for key in actual:assert actual[key]==certificate[key],key
assert actual['W_sym']==6 and actual['OPT_RC']==7
print(json.dumps({'new_cases':result['cases_checked'],'new_self_pairs':result['self_pairs_checked'],'old_profile_replayed':True,'old_W6_OPT7_replayed':True,'meaning':'bounded diagnostics only; no full-algorithm execution or independent proof review'},sort_keys=True))
