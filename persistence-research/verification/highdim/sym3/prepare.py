import sys
sys.dont_write_bytecode = True
from pathlib import Path

p = Path(__file__).with_name('continue_sym3.py')
s = p.read_text().replace('sym2/', 'sym3/').replace('continue_sym2.py', 'continue_sym3.py')
a = s.index('def reconcile():')
b = s.index('\ndef slices(', a)
s = s[:a] + '''def reconcile():
    source = HD / "hd2/results_t111132.json"
    baseline = read(source)
    remaining = {k:v for k,v in baseline.items() if v["status"].startswith("SKIPPED (k=")}
    counts = collections.Counter(len(v["far"]) for v in remaining.values())
    assert counts == {5:124, 6:66, 7:18, 8:2}, counts
    jobs = {"111132:"+k:dict(v,target=111132,key=k) for k,v in remaining.items()}
    for name,r in jobs.items():
        low = [(r["S_low"] // 10**i)%10+1 for i in range(3)]
        assert math.prod(low+[c//9+1 for c in r["far"]]) == 111132
    save(HERE/"assignment.json", {"label":"COMPUTED", "configurations":jobs,
         "baseline_count":len(baseline), "previously_closed":122,
         "assigned_by_k":dict(counts), "source_hashes":{str(source.relative_to(ROOT)):sha(source)}})
    print("assigned",len(jobs),"by k",dict(counts))

''' + s[b:]
a = s.index("    previous = HD / 'sym/standalone_checks.json'")
b = s.index("    for p in sorted((HERE / 'certs')", a)
s = s[:a] + s[b:]
a = s.index('def check_worker(path):')
b = s.index('\ndef checks(a):', a)
s = s[:a] + '''def check_worker(path):
    before = sha(path)
    start = time.monotonic()
    outputs, commands = {}, {}
    for label, script, extra in (("sym", HD/"sym/check_sym.py", []),
                                 ("F", HD.parent/"indep4/check_sym_F.py", ["--json"])):
        command = ["bash", "-c", 'ulimit -v 8000000; python3 -I "$@"',
                   "sym3-direct-check", str(script), str(path), "11"] + extra
        commands[label] = command
        try:
            proc = subprocess.run(command, text=True, capture_output=True, timeout=600)
            parsed = json.loads(proc.stdout.strip().splitlines()[-1])
            assert proc.returncode == 0 and parsed["result"] == "PASS", (proc.returncode, proc.stderr[-1000:], parsed)
            outputs[label] = parsed
        except Exception as e:
            outputs[label] = {"result":"FAIL", "error":repr(e)}
    assert sha(path) == before
    success = all(v["result"] == "PASS" for v in outputs.values())
    if success:
        assert sorted(outputs["sym"]["solutions"]) == sorted(outputs["F"]["claimed"])
    return {"result":"PASS" if success else "FAIL", "sha256":before,
            "commands":commands, "check":outputs["sym"], "independent":outputs["F"],
            "seconds":round(time.monotonic()-start,3)}

''' + s[b:]
s = s.replace('brute_Lmax=10)', "brute_Lmax=11, independent_checker_sha256=sha(HD.parent / 'indep4/check_sym_F.py'), direct_checker_sha256=sha(HD / 'sym/check_sym.py'))")
s = s.replace('for target in (32, 14112):', 'for target in (111132,):')
s = s.replace("stat['sha256'] = check['sha256']", "stat['sha256'] = check['sha256']\n        stat['auditor_actual_kills'] = check['independent']['kinds']\n        stat['auditor_kill_subtypes'] = check['independent']['ukinds']")
s = s.replace("'auditor_files': {str(p.relative_to(ROOT)): sha(p) for p in sorted((HD.parent / 'indep4').rglob('*')) if p.is_file()}", "'auditor_files': {str(p.relative_to(ROOT)): sha(p) for p in (HD.parent / 'indep4/check_sym_F.py', HD.parent / 'indep4/REPORT_F.md')}")
p.write_text(s)
