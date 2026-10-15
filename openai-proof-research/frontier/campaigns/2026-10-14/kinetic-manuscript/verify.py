"""Structural/authentication verification, not a mathematical proof checker.
Copyright (c) 2026 Myeongjin Kang. MIT License.
Writes only this package's validation.json and supporting-check receipts.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys, tempfile

HERE = Path(__file__).resolve().parent
p = argparse.ArgumentParser()
p.add_argument('--project-root', type=Path)
a = p.parse_args()
if a.project_root is None:
    a.project_root = next((ancestor for ancestor in HERE.parents
                           if (ancestor/'AGENTS.md').is_file()
                           and (ancestor/'sources/upstream.json').is_file()), None)
    if a.project_root is None:
        p.error('Cannot locate project root; pass --project-root /path/to/openai-proof-research')
checks = {}

def ck(name, condition):
    if not condition:
        raise AssertionError(name)
    checks[name] = True

def digest(data):
    return hashlib.sha256(data).hexdigest()

inputs = json.loads((HERE/'inputs.json').read_text())
for r in inputs:
    data = (a.project_root/r['path']).read_bytes()
    ck('input:'+r['path'], len(data) == r['bytes'] and digest(data) == r['sha256'])
subprocess.run([sys.executable, str(HERE/'verify_sources.py'), '--project-root', str(a.project_root)], check=True, capture_output=True)
ck('ten_pinned_H_sources', len(json.loads((HERE/'source-H.json').read_text())['files']) == 10)

tex = (HERE/'main.tex').read_text()
refs = (HERE/'references.tex').read_text()
labels = re.findall(r'\\label\{([^}]+)\}', tex)
ck('unique_TeX_labels', len(labels) == len(set(labels)))
used = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)
ck('all_TeX_references_resolve', set(used) <= set(labels))
citations = {x.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', tex) for x in group.split(',')}
ck('all_citations_resolve', citations <= set(re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}', refs)))
ck('TeX_environment_balance', sorted(re.findall(r'\\begin\{([^}]+)\}', tex)) == sorted(re.findall(r'\\end\{([^}]+)\}', tex)))
mapping = json.loads((HERE/'source-map.json').read_text())
for item in mapping:
    for label, number in item['main_tex_lines'].items():
        ck('source_map:'+label, r'\label{'+label+'}' in tex.splitlines()[number-1])
ck('source_map_25_claim_groups', len(mapping) == 25)
ck('initial_gradient_norm_correct', r'\norm{\nabla_xf_0}_{\Bol,2\beta}' in tex)
ck('fresh_factorials_visible', r'\mathfrak a_G=\mathfrak b_G\prod_i\frac1{j_i!}' in tex)
ck('structural_tie_explained', 'This is a structural tie on the extended chart, not\na null-set assertion. Strict' in tex)
ck('full_required_claim_groups', {'lem:window','lem:domination','lem:shear','lem:decorated','prop:micro','lem:chaining','thm:main'} <= set(labels))
meta = json.loads((HERE/'publication-metadata.json').read_text())
ck('author_no_affiliation', meta['author_names'] == ['Myeongjin Kang'] and meta['affiliations'] == [])
ck('no_acceptance_or_full_formal_claim', meta['acceptance_or_count_decision'] is False and meta['full_Lean_certificate'] is False)

for name, count in [('repair_checks',14),('editorial_checks',8),('adversarial_checks',None)]:
    run = subprocess.run([sys.executable, str(HERE/'checks'/f'{name}.py')], check=True, capture_output=True)
    result = json.loads((HERE/'checks'/f'{name}.json').read_text())
    ck('finite_support_run:'+name, run.returncode == 0)
    if count is not None:
        ck('finite_support_count:'+name, result['count'] == count and all(result['checks'].values()))
for name in ['repair_checks','adversarial_checks']:
    for extension in ['py','json']:
        ck('copied_repair_bytes:'+name+'.'+extension,
           (HERE/'checks'/f'{name}.{extension}').read_bytes() ==
           (a.project_root/'frontier/campaigns/2026-10-14/kinetic-repair-r1/checks'/f'{name}.{extension}').read_bytes())

info = subprocess.run(['pdfinfo', str(HERE/'output/pdf/main.pdf')], check=True, capture_output=True, text=True).stdout
pages = int(re.search(r'^Pages:\s+(\d+)', info, re.M).group(1))
ck('PDF_19_pages', pages == 19)
ck('PDF_author', 'Myeongjin Kang' in info)
log = (HERE/'output/pdf/main.log').read_text()
ck('no_TeX_warning_or_bad_box', not re.search(r'Warning|Overfull|Underfull|Undefined control|^!', log, re.M))
ck('all_page_renders_present', all((HERE/'qa'/f'page-{n:02}.png').is_file() for n in range(1,pages+1)))
qa = json.loads((HERE/'qa/visual-qa.json').read_text())
ck('all_page_visual_inspection_record', qa['inspected_pages'] == list(range(1,pages+1)) and qa['proof_verdict'] is False)
(HERE/'tmp').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='verify-', dir=HERE/'tmp') as temp:
    extracted = Path(temp)/'main.txt'
    subprocess.run(['pdftotext','-layout',str(HERE/'output/pdf/main.pdf'),str(extracted)], check=True)
    ck('extracted_text_matches_current_PDF', extracted.read_bytes() == (HERE/'qa/main.txt').read_bytes())

result = {'status':'PASS for structural/authentication checks only', 'check_count':len(checks),
          'input_count':len(inputs), 'claim_map_groups':len(mapping), 'PDF_pages':pages,
          'named_exact_support_checks':22, 'copied_counterchart_checks':'also rerun, byte-identical',
          'manuscript_gate':'independent review pending', 'full_mathematical_or_Lean_certificate':False,
          'checks':checks}
(HERE/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'checks'},indent=2))
