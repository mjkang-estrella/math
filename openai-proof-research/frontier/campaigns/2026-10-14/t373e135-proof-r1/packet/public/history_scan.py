"""Bounded-output history navigation; no mathematical or exclusion certificate.

Run from the project root. All outputs stay in this review root. Hidden and
ignored files and JSON are included; there is no text-file size cutoff.
"""
import datetime
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import re
import sys

PROJECT = Path.cwd()
OUT = Path(__file__).resolve().parents[1] / 'private'
FORBIDDEN = ['*structural*r142*', '*structural*r143*', '*arithmetic*r106*', 't373e135-*',
             'k369r134-*', 't088p133-*', 'discovery-analytic-r133-parent']
ACTIVE = re.compile(r'(?:structural|analytic).*r(?:13[5-9]|1[4-9]\d)|arithmetic.*r10[4-9]|t205q140|role[-_]?brief|brief.*r\d+', re.I)
COPIES = re.compile(r'review|contribution|publication|release|manuscript|formal|copied|corpus|inventory|snapshot|control[-_]?fixture|read[-_]?bindings', re.I)
OMIT = {'.git', '.venv', 'venv', 'node_modules', '__pycache__', '.lake',
        'outside', 'frozen', 'upstream', 'primary', 'sources', 'downloads',
        'download', 'extractions', 'renders', 'render', 'source', 'evidence',
        'inputs', 'input', 'vendor', 'dist', 'output', 'archive', 'archives',
        'discovery-analytic-r134-parent', 'fresh-analytic-discovery-r134'}
BINARY = {'.pdf', '.png', '.jpg', '.jpeg', '.gif', '.zip', '.gz', '.xz',
          '.zst', '.tar', '.pyc', '.olean', '.so', '.mp4', '.woff', '.sqlite', '.db'}
PAT = re.compile(r'Coulomb|Monge|multi.?marginal|repulsive.{0,35}transport|K.?\^?-?1.{0,30}covariance|covariance.{0,35}lift|transverse.{0,30}covariance|coupled.{0,30}(?:diffusion|Langevin)|flat.{0,20}boundar|stationary.{0,25}diffusion|constant.{0,25}diagonal.{0,20}covariance', re.I)
STRICT = '--strict' in sys.argv
if STRICT:
    OMIT.update({'private', 'context', 'canonical', 'preprints', 'fixtures', 'controls'})


def excluded(name):
    return (any(fnmatch.fnmatch(name.lower(), p) for p in FORBIDDEN)
            or ACTIVE.search(name) or COPIES.search(name) or name.lower() in OMIT)


def main():
    paths, pruned, hits, errors, binary = [], [], [], [], []
    total = 0
    for top in ['frontier', 'iterations', 'experiments', 'proposals', 'scouts', 'notes', 'findings']:
        base = PROJECT / top
        if not base.is_dir():
            continue
        for cur, dirs, files in os.walk(base, followlinks=False):
            kept = []
            for name in sorted(dirs):
                p = Path(cur) / name
                if excluded(name) or p.is_symlink():
                    pruned.append(p.relative_to(PROJECT).as_posix())
                else:
                    kept.append(name)
            dirs[:] = kept
            for name in sorted(files):
                if excluded(name):
                    continue
                p = Path(cur) / name
                if p.is_symlink() or p.suffix.lower() in BINARY:
                    continue
                rel = p.relative_to(PROJECT).as_posix()
                paths.append(rel)
                try:
                    with p.open('rb') as f:
                        if b'\0' in f.read(8192):
                            binary.append(rel)
                            continue
                    rows, count = [], 0
                    with p.open('rb') as f:
                        for lineno, raw in enumerate(f, 1):
                            total += len(raw)
                            line = raw.decode('utf-8', 'replace')
                            if PAT.search(line):
                                count += 1
                                if len(rows) < 8:
                                    rows.append({'line': lineno, 'excerpt': line[:700].rstrip(),
                                                 'line_bytes': len(raw), 'line_sha256': hashlib.sha256(raw).hexdigest()})
                    if count:
                        hits.append({'path': rel, 'matching_lines': count, 'first_hits': rows})
                except Exception as e:
                    errors.append({'path': rel, 'error': str(e)})
    result = {'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'forbidden_component_patterns': FORBIDDEN, 'active_regex': ACTIVE.pattern,
              'copy_regex': COPIES.pattern, 'other_omissions': sorted(OMIT),
              'binary_suffixes': sorted(BINARY), 'search_pattern': PAT.pattern,
              'paths': paths, 'pruned_directories': pruned, 'binary': binary,
              'text_bytes': total, 'hits': hits, 'errors': errors,
              'limits': 'Navigation only, bounded excerpts; no size cutoff; filters can omit authored history or admit copies; no perfect exclusion or exhaustive semantic-reading claim.'}
    name = 'history-search-strict.json' if STRICT else 'history-search.json'
    (OUT / name).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'paths': len(paths), 'text_bytes': total, 'hit_files': len(hits),
                      'errors': len(errors), 'receipt': 'packet/private/' + name}))
    for record in hits:
        if re.search(r'i217|i220|i35-splitting|entrop|langevin|coulomb', record['path'], re.I):
            print(record['path'], record['matching_lines'])


if __name__ == '__main__':
    main()
