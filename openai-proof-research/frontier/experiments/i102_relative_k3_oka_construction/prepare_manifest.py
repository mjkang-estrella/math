#!/usr/bin/env python3
"""Preparation only. Writes I102 evidence, never seals or edits source artifacts."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[3]
S = ROOT/'frontier/sources/i102_relative_k3_oka_construction'
E = ROOT/'frontier/experiments/i102_relative_k3_oka_construction'
OLD = ROOT/'frontier/sources/i98_complex_kahler_discovery'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def dump(path, obj):
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=2)+'\n')

def main():
    assert not (S/'seal.json').exists(), 'preparation after seal forbidden'
    domain = json.loads((ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json').read_bytes())
    bylocal = {x['local']:x for x in domain}
    primary = {x['text']:x for x in json.loads((OLD/'primary-manifest.json').read_bytes()) if 'text' in x}
    rows = []
    def add(local, lo, hi, purpose):
        p = ROOT/local
        raw = p.read_bytes();t=raw.decode(errors='replace');lines=t.split('\n')
        assert 1 <= lo <= hi <= len(lines), (local,lo,hi,len(lines))
        passage='\n'.join(lines[lo-1:hi])
        row={'local':local,'start':lo,'end':hi,'purpose':purpose,
             'line_convention':'LF split; formfeeds remain within a line; no appended newline',
             'sha256':sha(raw),'passage_sha256':sha(passage.encode()),
             'total_LF_lines':len(lines),'total_LF_newlines':raw.count(b'\n'),
             'total_splitlines':len(t.splitlines())}
        if local in bylocal:
            d=bylocal[local];row.update(upstream_path=d['path'],git_sha=d['git_sha'],
                url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['path'])
        elif local in primary:
            d=primary[local];row.update(url=d['url'],pdf_local=d['local'],pdf_sha256=d['sha256'])
        else:
            row['url']=None
        rows.append(row)
    k3='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Every-complex-K3-surface-is-Oka-September-23-2026/build/sections/'
    for f in ('introduction','local','sewing','degeneration','rational','gluing','globalization','projective','dynamics','dense'):
        local=k3+f+'.tex';n=len((ROOT/local).read_bytes().decode().split('\n'))
        add(local,1,n,'complete fixed-target theorem/lower-operation unit through ending; stipulated true, parameter applicability examined')
    ext='frontier/sources/i98_complex_kahler_discovery/external/'
    for name,ranges in {
        'larusson-2011.pdf.txt':[(1,408)],
        'kusakabe-2020.pdf.txt':[(1,180),(440,570),(670,755)],
        'xie-zhao-v2.pdf.txt':[(1,290),(430,574)],
        'kusakabe-matsumura.pdf.txt':[(1,150),(485,904),(927,969),(1282,1431)]
    }.items():
        for lo,hi in ranges:
            add(ext+name,lo,hi,'primary theorem/definition or complete used proof ending; references are not independently reproved')
    local='frontier/iterations/i98-complex-kahler-discovery.md'
    add(local,1,len((ROOT/local).read_bytes().decode().split('\n')),'complete original proof report, independently audited')
    for local in ('AGENTS.md','sources/upstream.json','frontier/experiments/i98-parent-verification.json',
                  'frontier/experiments/i98_complex_kahler_discovery/verify.py'):
        add(local,1,len((ROOT/local).read_bytes().decode().split('\n')),'complete rules/original evidence contract; no modification')
    snap='frontier/sources/i102_relative_k3_oka_construction/snapshots/'
    for path,lo,hi in [('README.md',1,3),('frontier/README.md',22,27),
                       ('frontier/TEN-FINDINGS.md',566,569),('frontier/iterations/README.md',1199,1207)]:
        add(snap+path,lo,hi,'history and current count/context screen only; no full ledger semantic reading')
    # Exact theorem screens actually printed in this round.
    statements=json.loads((OLD/'statement-screen.json').read_bytes())
    tokens=['Semialgebraic-universal','Universal-cover-splitting','The-abelianity',
        'Conditional-good-minimal-models-for-compact-Kahler-fourfolds-October-6',
        'Log-abundance-for-compact-Kahler-spaces-under-logarithmic-Iitaka-subadditivity-October-6',
        'Numerical-semiampleness-of-nef-adjoint-classes-on-compact-Kahler-manifolds-October-6',
        'Termination-of-generalized-log-canonical-flips-on-compact-Kahler-fourfolds-October-7']
    for r in statements:
        if r['path'].endswith('build/main.tex') or ('build/sections/' in r['path'] and any(x in r['path'] for x in tokens)):
            lo=r['LF_start'];hi=lo+r['text'].count('\n')
            add(r['local'],lo,hi,'statement-only companion screen, not full proof reading')
    dump(S/'read-manifest.json',rows)
    result=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],capture_output=True,text=True)
    dump(E/'diagnostic-preparation.json',{'command':[sys.executable,'-B',str(E/'diagnostics.py')],
        'exit_code':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
    assert result.returncode == 0
    dump(E/'diagnostic-results.json',json.loads(result.stdout))
    dump(S/'scope.json',{'pin':PIN,'original_blob_positions':10373,'manuscripts':749,
        'I14_originals':9340,'outside_originals':1033,'outside_PDF_texts':776,
        'domain_reference':'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json',
        'inherited_verifier':'frontier/experiments/i98_complex_kahler_discovery/verify.py',
        'primary_unique_PDF_replays':5,'pinned_PDF_replays':3,
        'independent_verdicts':{'A98':'ORIGINAL PASS WITHOUT REPAIRS',
            'W98':'ORIGINAL PASS WITHOUT REPAIRS in the reduced POPAI category',
            'moving_pole':'ORIGINAL PASS WITHOUT REPAIRS',
            'persistent_curve_class':'ORIGINAL PASS WITHOUT REPAIRS'},
        'new_bridge_status':{'G102':'author-level technical construction',
            'S102':'author-level technical parameter extension with uniform holomorphic-chain input',
            'E102':'proved sufficient exhaustion interface; relative extension hypothesis unproved'},
        'R98':'unproved and unrefuted','nomination':False,'accepted_count':8,'remaining':2})
    print(json.dumps({'read_records':len(rows),'diagnostics':json.loads(result.stdout)},indent=2))

if __name__ == '__main__':
    main()
