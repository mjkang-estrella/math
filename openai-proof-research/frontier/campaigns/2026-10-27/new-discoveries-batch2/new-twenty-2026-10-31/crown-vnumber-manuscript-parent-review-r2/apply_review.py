import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (60, 60))
resource.setrlimit(resource.RLIMIT_AS, (6*1024**3, 6*1024**3))
from pathlib import Path
import ast, json, subprocess
new = Path(__file__).resolve().parent
old = new.parent / 'crown-vnumber-manuscript-parent-review-r1'
source = (old / 'manuscript/generate_paper.py').read_text()
lines = source.splitlines(keepends=True)
def xa(i): return '*x*_{*a*_{%s}}' % i
def xb(i): return '*x*_{*b*_{%s}}' % i
def ya(i): return '*y*_{*a*_{%s}}' % i
def yb(i): return '*y*_{*b*_{%s}}' % i
def A_(i): return '*a*_{%s}' % i
def B_(i): return '*b*_{%s}' % i
context = dict(xa=xa, xb=xb, ya=ya, yb=yb, A_=A_, B_=B_)
def value(node):
    return eval(compile(ast.Expression(node), '<pure paragraph>', 'eval'),
                {'__builtins__': {}}, context)
def rep(text, before, after):
    assert text.count(before) == 1, (before, text[:100])
    return text.replace(before, after)
patches, changes, section = [], [], 0
for node in ast.parse(source).body:
    if not isinstance(node, ast.Expr) or not isinstance(node.value, ast.Call): continue
    call = node.value
    if not isinstance(call.func, ast.Name): continue
    kind = call.func.id
    if kind == 'h1':
        section += 1
        continue
    if kind not in ('p', 'proof', 'env'): continue
    label = value(call.args[1]) if kind == 'env' else ''
    if kind == 'env' and not label.startswith('Definition 2.3'): continue
    if kind == 'proof' and section not in (2, 5, 6): continue
    if kind == 'p' and section not in (1, 5, 6, 8, 10): continue
    if kind == 'p' and section == 8:
        if not ast.get_source_segment(source, call).startswith("p('The witnesses of this section"): continue
    text = value(call.args[2 if kind == 'env' else 0])
    before, ids, replacement = text, [], None
    if label.startswith('Definition 2.3'):
        text = rep(text, 'min{ <i>d</i> ≥ 1 : some homogeneous',
                   'min{ <i>d</i> ≥ 0 : some nonzero homogeneous')
        ids += ['F01']
    if kind == 'proof' and text.startswith('By [1, Corollary 2.2]'):
        text = rep(text, 'whose complements are <i>V</i> −',
                   'which are <i>T</i> = <i>V</i> −')
        text = rep(text, 'the mixed cut with deleted pair {<i>i</i>, <i>j</i>}',
                   'the mixed cut with surviving index pair {<i>i</i>, <i>j</i>}')
        a, b = text.index('Each displayed ideal is prime:'), text.index('Distinctness of the six families')
        text = text[:a] + ('Each displayed ideal is prime by the completed-component prime theorem '
            '[1, Section 3], applied to its disjoint completed components; isolated surviving '
            'coordinates remain free. ') + text[b:]
        ids += ['F02', 'F03']
    if section == 6 and kind == 'p' and text.startswith('If ' + B_('i') + ' ∈ <i>U</i>'):
        text = rep(text, 'since ' + A_('i') + ' and ' + B_('j') +
            ' ∈ <i>Y</i> − {' + B_('i') + '} lie in the block.',
            'since ' + A_('i') + ' and ' + B_('j') + ' lie in the block {' +
            A_('i') + '} ∪ (<i>Y</i> − {' + B_('i') + '}).')
        ids += ['F04']
    if section == 6 and kind == 'proof' and text.startswith('Work componentwise, and fix'):
        a, b = text.index('some coordinate '), text.index('and the only vertex of')
        text = text[:a] + 'some vertex of <i>X</i> has positive vertex degree, ' + text[b:]
        replacement = 'p(' + repr('<i>Proof.</i>&nbsp; ' + text) + ", 'proof')"
        ids += ['F08']
    if section == 5 and kind == 'proof' and text.startswith('Work componentwise (Lemma 4.1).'):
        replacement = 'p(' + repr('<i>Proof.</i>&nbsp; ' + text) + ", 'proof')"
        ids += ['F08']
    if ((section == 5 and kind == 'p' and text.startswith('These two quadrics')) or
        (section == 6 and kind == 'p' and text.startswith('Every component has now'))):
        text += ' □'
        ids += ['F08']
    if section == 5 and kind == 'proof' and text.startswith('Apply the symmetry that exchanges'):
        a = text.index('The image of a preimage f')
        text = text[:a] + ('Let σ denote this involution. Then σ(<i>f</i>) satisfies the '
            'hypothesis of Proposition 5.1 for <i>P</i>_{<i>X</i>}; hence σ(<i>f</i>) ∈ '
            '<i>P</i>_{<i>X</i>}, and applying σ again gives <i>f</i> ∈ <i>P</i>_{<i>Y</i>}.')
        ids += ['F08']
    if kind == 'p' and text.startswith('<b>Strategy and credit.</b>'):
        a, b = text.index('Every quartic witness'), text.index('No determinantal quotient')
        text = text[:a] + ('The nonempty-cut quartic witnesses in Section 8 follow [3, Proposition 5.2], '
            'up to relabeling and coordinate symmetry; its Q-case subscript slip is corrected '
            'by direct verification. The empty-prime monomial uses [3, Lemma 5.1] and '
            '[2, Proposition 3.6]. None of these witnesses is new. ') + text[b:]
        ids += ['F07']
    if section == 8 and kind == 'p' and text.startswith('The witnesses of this section'):
        a, b = text.index('They are the constructions'), text.index('Distinct indices')
        text = text[:a] + ('For nonempty cuts these are the constructions of [3, Proposition 5.2], '
            'up to relabeling and coordinate symmetry; its Q-case subscript slip is corrected '
            'explicitly below. The empty-prime monomial follows from the connected dominating '
            'set in [3, Lemma 5.1] and the construction [2, Proposition 3.6]. No witness is new. ') + text[b:]
        ids += ['F07']
    if section == 10 and kind == 'p' and text.startswith('<b>The source.</b>'):
        text = rep(text, 'the latter supplying the quartic witnesses used here',
                   'the latter supplying the nonempty-cut quartic witnesses up to relabeling and coordinate symmetry')
        text = rep(text, 'cited there from the colon-formula literature in the lineage of [7]; its proof',
                   'used there and derived directly in Section 3 of this draft; its proof')
        ids += ['F05', 'F07']
    if section == 10 and kind == 'p' and text.startswith('<b>Two-component cuts'):
        a, b = text.index('whose complements have two components:'), text.index('The full-side cuts')
        text = text[:a] + (
            'whose complements have two components. Under [4, Definition 4.6], the chosen vertices '
            'in each surviving component must form a connected dominating set in that component '
            'and also dominate the subgraph obtained by adjoining the deleted set <i>T</i>. '
            'For <i>Q</i>_{<i>i</i>}, the star-side choice must contain ' + A_('i') +
            ' and at least two distinct leaves ' + B_('j') + ', ' + B_('k') +
            ': with only ' + B_('j') + ', the deleted ' + A_('j') +
            ' is undominated, while two distinct leaves dominate every deleted X-vertex. '
            'The isolated ' + B_('i') + ' also dominates all deleted X-vertices, giving 3 + 1 = 4. '
            'For <i>M</i>_{<i>ij</i>}, both endpoints of each edge are required to dominate deleted '
            'vertices on both sides, giving 2 + 2 = 4. The <i>R</i>_{<i>i</i>} case is symmetric. ') + text[b:]
        a = text.index('the general upper bound, Theorem 3.5')
        text = text[:a] + (
            'the equality case in Theorem 3.5 of [4] requires radicality of '
            '<i>J</i>_{<i>G</i>} + <i>J</i>_{transversal}, not radicality of the colon itself. '
            'Identifying that sum with the colon is the missing equality step; degree information '
            'about a transversal alone does not supply it. No transfer across fields is stated there. '
            'Thus [4] does not supply the full-side or uniform positive-characteristic result.')
        ids += ['F06', 'F09']
    if section == 10 and kind == 'p' and text.startswith('<b>Summary of provenance.</b>'):
        text = rep(text, 'The quartic witnesses are due to [3, Proposition 5.2].',
            'The nonempty-cut quartic witnesses are due to [3, Proposition 5.2], up to relabeling '
            'and coordinate symmetry; the empty-prime witness uses [3, Lemma 5.1] and [2, Proposition 3.6].')
        ids += ['F07']
    if ids:
        if replacement is None:
            if kind == 'env':
                replacement = 'env(' + repr(value(call.args[0])) + ', ' + repr(label) + ', ' + repr(text) + ')'
            else:
                replacement = kind + '(' + repr(text) + ')'
        patches.append((node.lineno - 1, node.end_lineno, replacement + '\n'))
        changes.append(dict(ids=ids, original_line=node.lineno, before=before, after=text))
assert {i for c in changes for i in c['ids']} == {'F%02d' % i for i in range(1, 10)}
for a, b, replacement in reversed(patches): lines[a:b] = [replacement]
corrected = ''.join(lines)
ast.parse(corrected)
(new / 'manuscript/generate_paper.py').write_text(corrected)
(new / 'CORRECTIONS.json').write_text(json.dumps({
    'scope': 'Reviewer-prescribed F01-F09 manuscript/source corrections, main theorem and Lean-pending status unchanged',
    'edits': changes,
    'failed_setup': 'Initial in-memory general paragraph evaluation met an unrelated witness helper w; no generator/PDF was written. Restricted evaluation to targeted sections.'
}, indent=2) + '\n')
python = Path.home() / '.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3.12'
env = dict(os.environ, MALLOC_ARENA_MAX='2', PYTHONDONTWRITEBYTECODE='1', TMPDIR=str(new / 'tmp'))
result = subprocess.run([str(python), str(new / 'manuscript/generate_paper.py')],
    cwd=new, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=35)
(new / 'build.log').write_text(result.stdout)
assert result.returncode == 0, result.stdout
pdf = new / 'output/pdf/paper.pdf'
subprocess.run(['pdftotext', '-layout', str(pdf), str(new / 'paper.txt')], check=True, timeout=10)
subprocess.run(['pdftoppm', '-png', '-r', '120', str(pdf), str(new / 'page')], check=True, timeout=35)
print(json.dumps(dict(corrected_findings=sorted({i for c in changes for i in c['ids']}),
    edit_count=len(changes), pages=len(list(new.glob('page-*.png'))), pdf_bytes=pdf.stat().st_size)))
