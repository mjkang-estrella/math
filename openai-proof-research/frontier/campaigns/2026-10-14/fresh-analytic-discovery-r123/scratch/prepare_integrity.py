from pathlib import Path
r=Path(__file__).resolve().parents[1]
old=r.parent/'fresh-analytic-discovery-r122/packet/public'
v=(old/'verify.py').read_text().replace('r122','r123')
v=v.replace("require(e['type'] == 'blob' and e['sha'] == x['blob'] == blob and e['size'] == len(b),", "require(e['type'] == 'blob' and e['sha'] == x['blob'] == blob and e['size'] == x['size'] == len(b),")
v=v.replace("require(mapping[x['path']]['sha'] == x['blob'], 'removed canonical metadata mismatch')", "require(mapping[x['path']]['type'] == 'blob' and mapping[x['path']]['sha'] == x['blob'] and mapping[x['path']]['size'] == x['size'] and x['retained'] is False, 'removed canonical metadata mismatch')")
v=v.replace("        require(x['success'] is True and x['url'].startswith('https://arxiv.org/pdf/'), 'primary status/URL mismatch')\n        for key in ('pdf', 'text'):", "        require(x['url'].startswith('https://'), 'primary URL mismatch')\n        if x['success'] is False:\n            require(bool(x['failure']) and 'pdf' not in x and 'text' not in x, 'failed acquisition claims body')\n            continue\n        require(x['success'] is True, 'primary status mismatch')\n        for key in ('pdf', 'text'):")
v=v.replace("for register in ('history-register.json', 'context-register.json'):", "for register in ('history-register.json', 'context-register.json', 'render-register.json', 'search-register.json'):")
v=v.replace("'primary_pairs': len(primaries)","'primary_pairs': sum(x['success'] for x in primaries), 'primary_failures': sum(not x['success'] for x in primaries)")
v=v.replace('import argparse','''# Adapted from analytic r122 original integrity code; see RIGHTS.md.
import argparse''',1)
(r/'packet/public/verify.py').write_text(v)
c=(old/'controls.py').read_text().replace('R122','R123').replace("'nls-geometry.md'","'kohn-sham.md'").replace("'public/nls-geometry.md'","'public/kohn-sham.md'").replace('packet/public/nls-geometry.md','packet/public/kohn-sham.md').replace("'changed-source': 'sources'","'changed-source': 'upstream'")
c=c.replace("'baseline', 'wrong-final'", "'baseline', 'missing-final', 'wrong-final'")
c=c.replace("        z = subprocess.run(command,", "        if case == 'missing-final':\n            index = command.index('--finalhash'); del command[index:index+2]\n        z = subprocess.run(command,")
c=c.replace('import argparse','''# Adapted from analytic r122 original copied-control code; see RIGHTS.md.
import argparse''',1)
(r/'packet/public/controls.py').write_text(c)
print('prepared read-only verifier and disposable-copy controls')
