#!/usr/bin/env python3
"""Read-only byte identity check, not a Lean compiler or proof review."""
import argparse, hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--repo', type=Path, required=True)
    a = ap.parse_args()
    require(re.fullmatch('[0-9a-f]{64}', a.anchor), 'invalid external anchor')
    require(sha(HERE/'MANIFEST.json') == a.anchor, 'manifest anchor mismatch')
    data = json.loads((HERE/'MANIFEST.json').read_text())
    files = data['files']
    actual = {str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file()}
    require(actual == set(files) | {'MANIFEST.json'}, 'payload membership mismatch')
    for name, expected in files.items():
        f = HERE/name
        require(not f.is_symlink() and f.resolve().is_relative_to(HERE), 'unsafe payload path')
        require(sha(f) == expected, 'payload digest mismatch: '+name)
    binding = json.loads((HERE/'binding.json').read_text())
    require(binding['full_theorem_formalized'] is False, 'incorrect coverage status')
    for entry in binding['references']:
        require(sha(a.repo/entry['path']) == entry['sha256'], 'reference digest mismatch: '+entry['path'])
    receipt = json.loads((HERE/'validation/receipt.json').read_text())
    require(receipt['status'] == 'PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS', 'invalid build status')
    require(receipt['full_theorem_formalized'] is False, 'invalid full theorem claim')
    require(len(receipt['kernel_dependencies']) == 8, 'wrong declaration count')
    for axioms in receipt['kernel_dependencies'].values():
        require(set(axioms) <= {'propext','Classical.choice','Quot.sound'}, 'nonstandard axiom')
    for name,digest in receipt['sources'].items():
        require(sha(HERE/name) == digest, 'compiled source mismatch')
    for run in receipt['runs']:
        require(run['exit_code'] == 0, 'failed recorded compilation')
        require(sha(HERE/'validation'/(run['step']+'.log')) == run['output_sha256'], 'build log mismatch')
    print('PASS: exact payload, bound references, recorded scoped build; no full theorem certification')

if __name__ == '__main__':
    main()
