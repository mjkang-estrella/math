#!/usr/bin/env python3
"""Editorial/hash/build checks only; this is not a mathematical proof verifier.
Copyright (c) 2026 Myeongjin Kang. MIT License; see LICENSE-code.txt.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
checks = {}
def check(name, value):
    checks[name] = bool(value)
    if not value:
        raise AssertionError(name)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

tex = (HERE / 'main.tex').read_text()
refs = (HERE / 'references.tex').read_text()
labels = re.findall(r'\\label\{([^}]+)\}', tex)
check('unique_labels', len(labels) == len(set(labels)))
used = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)
check('resolved_internal_references', set(used) <= set(labels))
keys = set(re.findall(r'\\bibitem\{([^}]+)\}', refs))
cited = set(re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', tex))
check('resolved_bibliography', cited <= keys)
for env in ('document', 'theorem', 'lemma', 'proposition', 'proof', 'equation', 'align', 'align*'):
    check('balanced_' + env, tex.count('\\begin{' + env + '}') == tex.count('\\end{' + env + '}'))
source_map = json.loads((HERE / 'source-map.json').read_text())
check('all_source_map_labels_resolve', all(label in labels for item in source_map for label in item['manuscript_labels']))
check('exact_author_and_no_affiliation', '\\author{Myeongjin Kang\\thanks{' in tex and '\\affiliation' not in tex)
check('explicit_no_full_lean_certificate', 'No full Lean certificate exists' in tex)
check('finite_N_before_outer_limit', 'At fixed $j$, let $N\\to\\infty$' in tex)
check('ordinary_transpose_and_order_displayed', 'Q(z)=\\tfrac12S_E^{-1}U^*\\mathcal M(z)^{\\mathsf T}V' in tex)
check('explicit_hermitian_tangent_determinant', '\\det(sI+u\\Rea B+v\\Ima B)=0' in tex)
check('explicit_full_level', '\\{z\\in\\C:|f(z)|=1\\}=\\partial K' in tex)

frozen = {
 'frontier/campaigns/2026-10-14/matrix-disk-discovery/analysis.md': 'e74dda6b866d7780b57911aef30a2bfb99589e7036864b1da6a302072ab462b6',
 'frontier/campaigns/2026-10-14/matrix-disk-proof-r1/review.md': 'c1b09f8ad9d05d4b0d323079871b4cfb1e0f2084b41b6e5b0d07f8029288c6c7',
 'frontier/campaigns/2026-10-14/matrix-disk-contribution-r1/review.md': 'd317e565614f3babf2c03e5c6e7b5f4980c31ab28f7e2059b01adc1c8f932df5',
}
for path, digest in frozen.items():
    check('frozen_' + Path(path).parent.name, sha(ROOT / path) == digest)
for name, src, copied, result, count in (
 ('discovery', 'frontier/campaigns/2026-10-14/matrix-disk-discovery/check.py', 'checks/discovery/check.py', 'checks/discovery/checks.json', 17),
 ('reviewer', 'frontier/campaigns/2026-10-14/matrix-disk-proof-r1/supplemental-check.py', 'checks/reviewer/supplemental-check.py', 'checks/reviewer/supplemental-checks.json', 16),
):
    check(name + '_checker_byte_identical', sha(ROOT / src) == sha(HERE / copied))
    data = json.loads((HERE / result).read_text())
    check(name + '_exact_support_output', data['status'] == 'PASS' and data['count'] == count and all(data['checks'].values()))
log = (HERE / 'output/pdf/main.log').read_text()
check('warning_free_tex_log', not re.search(r'LaTeX Warning|Package .* Warning|Overfull|Underfull|undefined references|Undefined control sequence', log))
info = subprocess.run(['pdfinfo', str(HERE / 'output/pdf/main.pdf')], check=True, capture_output=True, text=True).stdout
pages = int(re.search(r'^Pages:\s+(\d+)', info, re.M).group(1))
check('eleven_page_pdf', pages == 11)
check('pdf_author_metadata', re.search(r'^Author:\s+Myeongjin Kang$', info, re.M))
check('all_pages_rendered', len(list((HERE / 'qa').glob('page-*.png'))) == pages)
check('pdf_text_has_no_unresolved_markers', '??' not in (HERE / 'qa/main.txt').read_text())

validation = {
 'status': 'PASS',
 'scope': 'Editorial, frozen source binding, exact finite supporting checks, TeX build and PDF structure only; not independent mathematical review.',
 'checks': checks,
 'count': len(checks),
 'build': {'engine': 'Tectonic 0.17.0', 'pdf_pages': pages, 'tex_warnings': 0},
 'visual_qa': {'method': 'pdftoppm -r 105 -png; all eleven individual PNG pages visually inspected by manuscript agent', 'pages_inspected': list(range(1, pages + 1)), 'defects_observed': [], 'automated_visual_proof': False},
 'mathematical_status': {'frozen_discovery_proof': 'independent PASS, no repairs', 'contribution': 'independent SUBSTANTIAL, one package, bounded primary coverage', 'new_manuscript_gate': 'pending independent parent review', 'accepted_by_this_package': False},
 'formalization': {'full_Lean_certificate': False, 'pending_external_support_used': False},
 'remaining_risks': ['Independent review must check this newly typeset presentation.', 'Upstream complete/Faber theorem and Jin geometric inputs are explicit premises.', 'Primary literature coverage is bounded; worldwide priority is not established.', 'No full analytic Lean formalization or public submission is certified.'],
}
(HERE / 'validation.json').write_text(json.dumps(validation, indent=2) + '\n')
records = [{'path': str(p.relative_to(HERE)), 'sha256': sha(p), 'bytes': p.stat().st_size} for p in sorted(HERE.rglob('*')) if p.is_file() and p.name != 'outputs.json']
(HERE / 'outputs.json').write_text(json.dumps({'manifest_excludes_itself': True, 'files': records}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'editorial_checks': len(checks), 'finite_support_checks': 33, 'pdf_pages': pages, 'tex_warnings': 0, 'manifest_files': len(records)}))
