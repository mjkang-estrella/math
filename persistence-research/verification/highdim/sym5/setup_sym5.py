"""One-time, reproducible minimal edits to copied sym4 scripts."""
import pathlib
import difflib
import hashlib
import json

H = pathlib.Path(__file__).resolve().parent
S = H.parent / 'sym4'

def edit(name, replacements, source=None):
    original = (S / (source or name)).read_text()
    text = original
    for old, new in replacements:
        assert old in text, (name, old)
        text = text.replace(old, new)
    (H / name).write_text(text)
    (H / (name + '.diff')).write_text(''.join(difflib.unified_diff(
        original.splitlines(True), text.splitlines(True),
        fromfile='sym4/' + (source or name), tofile='sym5/' + name)))

edit('gen_sym.py', [
    ('self.pin_digits=min(pin_digits,qmin)',
     '# SYM5: reject over-pinning instead of silently reducing the request.\n'
     '        assert type(pin_digits) is int and 0 <= pin_digits <= qmin, "decimal pin depth"\n'
     '        self.pin_digits=pin_digits'),
    ("type=int,choices=(0,1,2,3),default=3", "type=int,default=3"),
])

edit('check_sym5.py', [
    ("require(type(self.pin_digits) is int and 0<=self.pin_digits<=min(3,self.qmin),'decimal pin depth')",
     "# SYM5: the domain proves any decimal depth up to qmin.\n"
     "        require(type(self.pin_digits) is int and 0<=self.pin_digits<=self.qmin,'decimal pin depth')"),
    ('seq=[1]\n                v=base%modulus', 'seq=[1]; seen={1}  # SYM5: linear cycle membership\n                v=base%modulus'),
    ("require(v not in seq,'non-unit decimal cycle')\n                    seq.append(v);v=v*base%modulus",
     "require(v not in seen,'non-unit decimal cycle')\n                    seq.append(v);seen.add(v);v=v*base%modulus"),
    ('for ar,u in enumerate(seq3):\n                for wr,v in enumerate(seq7):\n                    if u*v%modulus!=(self.K//2**self.t)%modulus: continue',
     '# SYM5: exact join of the same Cartesian pairs, without quadratic scanning.\n'
     '            by_value=collections.defaultdict(list)\n'
     '            for wr,v in enumerate(seq7): by_value[v].append(wr)\n'
     '            for ar,u in enumerate(seq3):\n'
     '                wanted=(self.K//2**self.t)*pow(u,-1,modulus)%modulus\n'
     '                for wr in by_value[wanted]:'),
], source='check_sym.py')

edit('continue_sym2.py', [
    ('confined to sym2/', 'confined to sym5/'),
    ("source = HD/'sym2/summary.json'", "source = HD/'sym4/summary.json'"),
    ("previous = read(HD/'sym2/assignment.json')", "previous = read(HD/'sym4/assignment.json')"),
    ('assert len(keys)==134', 'assert len(keys)==95'),
    ("'expected':134", "'expected':95"),
    # A module-local minimum used only by this search process and its slicers.
    ('\nLIBRARY = {}\n', '\nLIBRARY = {}\nMIN_FLOOR = 3\n'),
    ('max(3, valuation(K, 2) + 1 + extra_floor)', 'max(MIN_FLOOR, valuation(K, 2) + 1 + extra_floor)'),
    ("previous = HD / 'sym2/kill_usage.json'", "previous = HD / 'sym4/kill_usage.json'"),
    ('    signal.signal(signal.SIGALRM, alarm)\n    signal.setitimer',
     '    global MIN_FLOOR\n    MIN_FLOOR = max(3, pin_digits)  # SYM5: explicitly cover low positions\n'
     '    signal.signal(signal.SIGALRM, alarm)\n    signal.setitimer'),
    ("'check_sym.py'", "'check_sym5.py'"),
    ("'gen_sym.py', 'gen_precomputed.py', 'check_sym5.py', 'continue_sym2.py'", "'gen_sym.py', 'gen_precomputed.py', 'check_sym5.py', 'continue_sym2.py'"),
    ('default=12)', 'default=10)'),
    ('1 <= a.workers <= 12', '1 <= a.workers <= 10'),
    # Use the copied audit/check functions directly; finalization adds F replay.
    ("    elif a.mode == 'check':\n        subprocess.run(['bash','-c','ulimit -v 8000000; python3 -I \"$@\"','sym4-replay',\n                        str(HERE/'replay_dual.py'),'--workers',str(a.workers)],check=True)\n    else:\n        subprocess.run(['bash','-c','ulimit -v 8000000; python3 -I \"$@\"','sym4-coverage',\n                        str(HERE/'audit_coverage.py')],check=True)",
     "    elif a.mode == 'check': checks(a)\n    else: audit()"),
])

sources = ['gen_sym.py','gen_precomputed.py','check_sym.py','continue_sym2.py',
           'audit_coverage.py','coverage_distinct.py','supply.json','summary.json']
(H / 'source_hashes.json').write_text(json.dumps({str(S / p):hashlib.sha256((S / p).read_bytes()).hexdigest()
                                               for p in sources}, indent=1)+'\n')
