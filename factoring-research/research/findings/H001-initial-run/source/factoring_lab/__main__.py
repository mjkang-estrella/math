import argparse
import json
from pathlib import Path

from .algorithms import ALGORITHMS
from .runner import ROOT, iterate, run_one, verify_run


def main() -> None:
    p = argparse.ArgumentParser(description="One bounded, reproducible factoring experiment at a time")
    sub = p.add_subparsers(dest="command", required=True)
    it = sub.add_parser("iterate", help="freeze a hypothesis and run one configured experiment wave")
    it.add_argument("--hypothesis", required=True)
    it.add_argument("--config", type=Path, default=ROOT / "configs/smoke.json")
    it.add_argument("--output", type=Path)
    one = sub.add_parser("factor", help="run one baseline with hard wall-clock timeout")
    one.add_argument("n", type=int)
    one.add_argument("--algorithm", choices=ALGORITHMS, default="rho")
    one.add_argument("--seed", type=int, default=11)
    check = sub.add_parser("verify-run", help="check hashes and all successful factor witnesses")
    check.add_argument("folder", type=Path)
    args = p.parse_args()
    try:
        if args.command == "iterate":
            print(iterate(args.config, args.hypothesis, args.output))
        elif args.command == "verify-run":
            verify_run(args.folder)
            print("Run hashes and factor witnesses verified.")
        else:
            if args.n < 0 or args.n.bit_length() > 4096:
                raise ValueError("n must be nonnegative and at most 4096 bits")
            print(json.dumps(run_one(args.algorithm, args.n, args.seed,
                                     {"max_events": 20000, "max_operand_bits": 16384}, 2.0), indent=2))
    except (ValueError, OSError) as exc:
        p.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    main()

