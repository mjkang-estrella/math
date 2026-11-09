# Corrected crown ordinary-proof draft

DRAFT; MathDB369163; Lean endpoint PENDING; credit0, accepted count52/60.
The parent made presentation-only corrections listed in CORRECTIONS.json, preserving all author bytes. All nine final pages were rendered at120dpi and visually inspected. The mathematical draft remains subject to manuscript review and full Lean certification.

Build with the existing ReportLab4.4.9 runtime:
    timeout 60 python3 -I -B -c "import os,resource,subprocess; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(50,50)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3)); subprocess.run([os.path.expanduser('~/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3.12'),'manuscript/generate_paper.py'],check=True,timeout=40)"
Run from this lane. No package installation or network required. Fonts are the same existing system LiberationSerif/Symbola paths as the original generator.

The original source coverage map and frozen inputs are retained. Their source evidence paths are absolute paths to immutable existing research lanes. The historical author runner is not included as an enforced resource guarantee; see CORRECTIONS.json. Parent successful build used actual two-CPU affinity, CPU60/AS6GiB, a35s generator subprocess timeout and35s render timeout, not a full cgroup/RSS attestation. Failed label-validation build logs remain separate from the successful build.log. No Lean certificate or source-only Lean ZIP exists here.
