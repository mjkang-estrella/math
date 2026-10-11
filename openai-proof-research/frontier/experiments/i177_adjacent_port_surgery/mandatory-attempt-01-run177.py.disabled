"""Exclusive development captures, including failed sources and empty streams."""
import json
from pathlib import Path
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
mode = sys.argv[1]
if mode == "--child":
    mode = sys.argv[2]
    for name in ("math177.py", "research177.py"):
        path = BASE / name
        exec(compile(path.read_bytes(), str(path), "exec"), globals())
    print(json.dumps(globals()[mode](), indent=2, sort_keys=True))
else:
    i = 1
    while (BASE / f"{mode}-attempt-{i:02d}-receipt.json").exists():
        i += 1
    prefix = f"{mode}-attempt-{i:02d}"
    for name in ("math177.py", "research177.py", "run177.py"):
        with (BASE / (prefix + "-" + name + ".disabled")).open("xb") as f:
            f.write((BASE / name).read_bytes())
    start = time.perf_counter()
    result = subprocess.run([sys.executable, "-I", "-B", str(BASE / "run177.py"),
                             "--child", mode], capture_output=True)
    elapsed = time.perf_counter() - start
    for suffix, data in ((".json", result.stdout), ("-stderr.txt", result.stderr)):
        with (BASE / (prefix + suffix)).open("xb") as f:
            f.write(data)
    receipt = {"mode": mode, "returncode": result.returncode, "seconds": elapsed,
               "stdout_size": len(result.stdout), "stderr_size": len(result.stderr)}
    with (BASE / (prefix + "-receipt.json")).open("x") as f:
        json.dump(receipt, f, sort_keys=True, indent=2)
    print(json.dumps(receipt))
    if result.returncode:
        print(result.stderr.decode(), file=sys.stderr)
    sys.exit(result.returncode)
