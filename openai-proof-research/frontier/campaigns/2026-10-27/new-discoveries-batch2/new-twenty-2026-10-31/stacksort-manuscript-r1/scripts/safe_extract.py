#!/usr/bin/env python3
"""Safe-extraction test of the source-only Lean ZIP. Does NOT run Lean.

Usage: python3 -I scripts/safe_extract.py <zip> <outdir> <r6-results.json> <report.json>
Checks: expected sha256; every member a regular file with a relative path, no
'..', no absolute path, no backslash, no duplicate, no symlink/special mode,
no compiled Lean or object artifacts; bounded sizes; extraction confined to
outdir; extracted bytes hash-identical to the ZIP members; every .lean module
hash equals the round-6 results.json record; the six round-6 endpoint names
occur in StackSortFinal6.lean; no sorry/admit/axiom/native_decide/unsafe tokens.
"""
import hashlib, json, re, stat, sys, zipfile
from pathlib import Path, PurePosixPath

EXPECT = '9b734e2fe521651fd33bbf92bdf05f1b542a6aeb82f90d2cd1e13399d6cf5c2f'
BAD_EXT = {'.olean', '.ilean', '.trace', '.hash', '.c', '.o', '.so', '.a', '.exe', '.dll'}
ENDPOINTS = ['mathdb_345545', 'limit_ge', 'nonvacuity', 'subsequence_companion',
             'mathdb_345545_max', 'max_companion']


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    zp, out, res, rep = map(Path, sys.argv[1:5])
    zb = zp.read_bytes()
    r = {'zip': str(zp.name), 'zip_sha256': sha(zb), 'expected_sha256': EXPECT,
         'zip_hash_matches': sha(zb) == EXPECT, 'members': [], 'problems': []}
    out.mkdir(parents=True, exist_ok=False)
    names = set()
    with zipfile.ZipFile(zp) as z:
        infos = z.infolist()
        r['member_count'] = len(infos)
        r['testzip_first_bad'] = z.testzip()
        total = 0
        for i in infos:
            n = i.filename
            mode = (i.external_attr >> 16) & 0o177777
            pp = PurePosixPath(n)
            prob = []
            if n.startswith('/') or '\\' in n or ':' in n:
                prob.append('absolute_or_odd_path')
            if any(part in ('..', '') for part in pp.parts):
                prob.append('dotdot_or_empty_component')
            if n in names:
                prob.append('duplicate')
            names.add(n)
            if mode and stat.S_ISLNK(mode):
                prob.append('symlink')
            if mode and not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                prob.append('special_mode')
            if pp.suffix in BAD_EXT:
                prob.append('compiled_artifact')
            if i.file_size > 5_000_000:
                prob.append('oversize')
            total += i.file_size
            if n.endswith('/'):
                r['members'].append({'name': n, 'dir': True, 'problems': prob})
                continue
            data = z.read(i)
            dest = (out / n).resolve()
            if out.resolve() not in dest.parents:
                prob.append('escapes_outdir')
            elif not prob:
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)
                if sha(dest.read_bytes()) != sha(data):
                    prob.append('extract_mismatch')
            r['members'].append({'name': n, 'bytes': i.file_size, 'sha256': sha(data),
                                 'mode': oct(mode), 'problems': prob})
            if prob:
                r['problems'].append({n: prob})
        r['total_uncompressed_bytes'] = total
    files = [m for m in r['members'] if not m.get('dir')]
    lean = [m for m in files if m['name'].endswith('.lean')]
    r['file_count'] = len(files)
    r['lean_module_count'] = len(lean)
    r['other_files'] = sorted(m['name'] for m in files if not m['name'].endswith('.lean'))
    rec = json.loads(res.read_text())['modules']
    by_base = {PurePosixPath(m['name']).name: m for m in lean}
    cmp = {'recorded_in_results': len(rec), 'matched': 0, 'mismatched': [], 'missing_in_zip': [],
           'zip_not_in_results': sorted(set(by_base) - set(rec))}
    for k, v in rec.items():
        if k not in by_base:
            cmp['missing_in_zip'].append(k)
        elif by_base[k]['sha256'] == v['sha256']:
            cmp['matched'] += 1
        else:
            cmp['mismatched'].append(k)
    r['results_json_module_hash_comparison'] = cmp
    # tokens are scanned outside comments and string literals
    tok = re.compile(r'\b(sorry|admit|native_decide|unsafe|implemented_by|extern)\b|^\s*axiom\b', re.M)
    hits = []
    for m in lean:
        txt = (out / m['name']).read_text(encoding='utf-8')
        nocomment = re.sub(r'/-.*?-/', '', txt, flags=re.S)
        nocomment = re.sub(r'--[^\n]*', '', nocomment)
        nocomment = re.sub(r'"(?:[^"\\\n]|\\.)*"', '""', nocomment)  # string literals (audit JSON keys)
        for t in tok.finditer(nocomment):
            hits.append({'file': m['name'], 'token': t.group(0).strip()})
    r['forbidden_token_hits_outside_comments'] = hits
    fin = [m for m in lean if m['name'].endswith('StackSortFinal6.lean')]
    if fin:
        txt = (out / fin[0]['name']).read_text(encoding='utf-8')
        r['StackSortFinal6'] = {'path': fin[0]['name'], 'sha256': fin[0]['sha256'],
                                'endpoints_declared': {e: bool(re.search(r'theorem\s+' + e + r'\b', txt)) for e in ENDPOINTS},
                                'namespace_Round6': 'namespace StackSort.Round6' in txt}
    r['lean_lake_leanchecker_executed'] = False
    r['PASS'] = (r['zip_hash_matches'] and not r['problems'] and r['testzip_first_bad'] is None
                 and not cmp['mismatched'] and not cmp['missing_in_zip'] and not hits
                 and r.get('StackSortFinal6', {}).get('namespace_Round6', False)
                 and all(r.get('StackSortFinal6', {}).get('endpoints_declared', {}).values()))
    rep.write_text(json.dumps(r, indent=1) + '\n')
    print(json.dumps({k: r[k] for k in ('zip_sha256', 'member_count', 'file_count', 'lean_module_count', 'other_files', 'PASS')}))
    print(json.dumps(cmp)); print(json.dumps(r.get('StackSortFinal6'))); print('hits', hits[:10]); print('problems', r['problems'][:10])


if __name__ == '__main__':
    main()
