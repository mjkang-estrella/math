#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Log and reference checks, not a visual or mathematical review."""
from pathlib import Path
import re,json,sys
r=Path(sys.argv[1]);p=r/'packet/public';log=(r/'build/tex/main.log').read_text(errors='replace')
tex='\n'.join(f.read_text() for f in p.glob('*.tex') if f.name!='references.tex');bib=(p/'references.tex').read_text()
keys=set(re.findall(r'\\bibitem\{([^}]+)\}',bib))
cites=set(k.strip() for x in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',tex) for k in x.split(','))
labels=re.findall(r'\\label\{([^}]+)\}',tex)
refs=set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',tex))
problems=[x for x in log.splitlines() if re.search(r'Overfull|undefined|multiply defined|LaTeX Warning|Package .*Warning|Missing character|^!',x)]
result={'missing_citation_keys':sorted(cites-keys),'missing_labels':sorted(refs-set(labels)),'duplicate_labels':sorted(k for k in set(labels) if labels.count(k)>1),'log_issues':problems,'underfull_lines':[x for x in log.splitlines() if 'Underfull' in x]}
(r/'build/log-qa.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
if any(result[k] for k in ['missing_citation_keys','missing_labels','duplicate_labels','log_issues']): sys.exit(1)
