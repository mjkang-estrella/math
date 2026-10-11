"""Retained performance diagnostic on one already-certified candidate."""
import cProfile
import io
import json
from pathlib import Path
import pstats
import sys
import types

ROOT = Path(__file__).resolve().parents[3]
EXP = ROOT / "frontier/experiments/i173_brace_high_loss_octagons"
runner = types.ModuleType("runner")
runner.__file__ = str(EXP / "run.py")
exec(compile((EXP / "run.py").read_bytes(), runner.__file__, "exec"), runner.__dict__)
research = runner.load()
research.mandatory()
records = json.loads((EXP / "surgeries-attempt-01.json").read_bytes())["records"]
record = max(records, key=lambda r: len(r["cycles"]))
t = sys.modules["toolkit"]
profiler = cProfile.Profile()
profiler.enable()
result = t.analyze(record["graph"], record["row"]["step"])
t.certify_graph(record["graph"])
t.brace_certificate(record["graph"])
t.cuts3(record["graph"])
profiler.disable()
assert result["row"] == record["row"]
stream = io.StringIO()
pstats.Stats(profiler, stream=stream).sort_stats("cumulative").print_stats(30)
with (EXP / "profile-result.txt").open("x") as out:
    out.write("PASS: identical exact row, largest cycle-count candidate\n")
    out.write(json.dumps(dict(m=record["m"], history=record["history"])) + "\n")
    out.write(stream.getvalue())
print(stream.getvalue())
