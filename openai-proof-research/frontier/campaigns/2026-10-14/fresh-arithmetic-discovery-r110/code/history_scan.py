"""Bounded authored-history navigation; never a clearance certificate."""
import os, re, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT.parents[3]
ACTIVE = re.compile(r'h138-|analytic.*r13[89]|t185r144-|structural.*r14[45]', re.I)
BROAD = re.compile(r'arithmetic.*r10[789]|structural.*r143|t177c143-|analytic.*r13[567]|t373e135-|k369r134-|t088p133-', re.I)
# Deliberately coarse. Applied to EVERY component before descent/body selection.
ROLES = re.compile(r'review|proof-r\d|contribution|correctness|formal|manuscript|release|publication|source|primary|literature|search|history|extract|render|vendor|frozen|outside|copy|copied|corpus|inventor|fixture|control|intake|brief|packet|payload|integrity|manifest|hash|receipt|cache|download|scratch|private|context|inputs|external|bibliograph|reference|metadata|catalog|contents|readme|\.git|node_modules|\.venv|__pycache__|prepare|record.read|handoff|tasks\.json|dispatch|launch|transcript|session|log\.json|acquisition|author.unchanged|family.titles|authentication|task(?:s)?[.-]|proof(?:[._-]|$)', re.I)
NEW = re.compile(r'(?:discovery|parent|arithmetic|analytic|structural).*r(?:1\d\d|[2-9]\d\d)', re.I)
TERM = re.compile(r'Kurosh|division.ring|algebraic division|\bI201\b|\bT201\w*|bounded.degre.{0,40}division|locally.finite.{0,40}division', re.I)

def excluded(name):
    return bool(ACTIVE.search(name) or BROAD.search(name) or ROLES.search(name) or NEW.search(name))

def main():
    hits, omissions, errors = [], [], []
    read = 0
    for base in ['campaigns', 'iterations', 'experiments', 'proposals', 'scouts', 'notes', 'findings']:
        start = PROJECT / 'frontier' / base
        if not start.exists():
            errors.append({'path': str(start), 'reason': 'absent'})
            continue
        for here, ds, fs in os.walk(start, followlinks=False):
            for d in list(ds):
                q = Path(here)/d
                if excluded(d) or q.is_symlink():
                    ds.remove(d); omissions.append(str(q.relative_to(PROJECT)))
            for f in fs:
                q = Path(here)/f
                if excluded(f) or q.is_symlink():
                    omissions.append(str(q.relative_to(PROJECT))); continue
                try:
                    b = q.read_bytes()
                    if b'\0' in b: continue
                    s = b.decode('utf-8')
                except (OSError, UnicodeDecodeError): continue
                read += 1
                found = [{'line': i, 'text': t} for i,t in enumerate(s.splitlines(),1) if TERM.search(t)]
                if found: hits.append({'path': str(q.relative_to(PROJECT)), 'bytes': len(b), 'hits': found})
    data = {'utf8_files_no_size_cutoff': read, 'omissions': omissions, 'errors': errors, 'hits': hits}
    (ROOT/'private/search/kurosh-history.json').write_text(json.dumps(data,indent=2))
    print(json.dumps({'read': read, 'omitted_paths': len(omissions), 'hits': [{'path':x['path'],'lines':[v['line'] for v in x['hits']]} for x in hits], 'errors': errors},indent=2))

if __name__ == '__main__': main()
