import sys, os, json, time, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
bad = [l.strip() for l in open(os.path.join(HERE, 'bad_paths.txt')) if l.strip()]
print(len(bad), 'non-pass files')
for p in bad:
    for tag, checker in (('f5  ', os.path.join(HERE, 'check_sym_F5.py')),
                         ('base', os.path.join(HERE, 'check_sym_F_base.py'))):
        cmd = ['bash', '-c', 'ulimit -v 6000000; python3 -I "%s" "%s" 11 --json' % (checker, p)]
        t = time.time()
        try:
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=2400)
            d = json.loads(out.stdout.strip().splitlines()[-1])
            print('%s %-8s wall %6.1f  %s' % (tag, d['result'], time.time() - t,
                  (d.get('problems') or [''])[0][:80]), os.path.basename(p), flush=True)
        except Exception as e:
            print('%s ERROR %s' % (tag, e), os.path.basename(p), flush=True)
