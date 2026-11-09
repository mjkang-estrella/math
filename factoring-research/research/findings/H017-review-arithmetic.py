"""One frozen exact-fraction audit. No polynomial, root, or population inputs."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import signal
import time

BASE = Path(__file__).resolve().parent
PROTOCOL = BASE / "H017-review-arithmetic-protocol.json"
OUTPUT = BASE / "H017-review-arithmetic-results.json"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    protocol = json.loads(PROTOCOL.read_text())
    if OUTPUT.exists():
        raise SystemExit("Refusing to overwrite an earlier run")
    start = time.monotonic()
    records = [{"id": key, "status": "unstarted"} for key in protocol["cases"]]
    result = {
        "kind": "exact arithmetic proof audit, not geometric experiment",
        "protocol_sha256": digest(PROTOCOL),
        "source_sha256": digest(Path(__file__)),
        "records": records,
    }

    def save():
        result["elapsed_seconds"] = time.monotonic() - start
        result["status_counts"] = {
            s: sum(r["status"] == s for r in records)
            for s in ("pass", "fail", "error", "timeout", "unstarted")
        }
        OUTPUT.write_text(json.dumps(result, indent=2) + "\n")

    def stop(signum, frame):
        result["interrupted_signal"] = signum
        save()
        raise SystemExit(124)

    signal.signal(signal.SIGTERM, stop)
    save()
    paths = {"source": Path(__file__), "input": BASE / "H017-tail-provenance.json",
             "report": BASE / "H017-resultant-tail-supply.md"}
    for key, path in paths.items():
        if digest(path) != protocol[key + "_sha256"]:
            result["preflight_error"] = "Frozen hash mismatch: " + key
            save()
            raise SystemExit(2)

    a, b, delta, Q, K = F(153, 200), F(189, 200), F(21, 10), F(9, 5), F(11, 5)
    q = Q / delta**2
    u = b + (K / delta + a * delta) / (3 * b)
    s = max(3 * a - q, 2 * a)
    rho = 1 / (a * delta**2)
    beta0 = a - q
    beta = beta0 / (1 - rho)
    finite = 3 * F(4, 5) * a
    calculated = {
        "a": a, "b": b, "delta": delta, "Q": Q, "K": K,
        "q": q, "u_required": u, "H013_upper_exponent": s,
        "old_gap": s - u, "rho_uniform_upper": rho,
        "small_height_rho0": beta0,
        "primitive_upper_rho0_lambda0": 3 * beta0,
        "lambda_critical_rho0": u / 3 - beta0,
        "beta_uniform": beta,
        "primitive_upper_uniform_lambda0": 3 * beta,
        "lambda_critical_uniform": u / 3 - beta,
        "finite_primitive_exponent": finite, "finite_model_gap": u - finite,
        "lambda_finite_rho0": F(4, 5) * a - beta0,
        "lambda_finite_uniform": F(4, 5) * a - beta,
        "reducible_exponent": 2 * a,
    }
    expected = json.loads(paths["input"].read_text())["exact_constant_checks"]
    extra = {
        "strict_chain": (2 * a < finite < u < s < 2 * b, True),
        "uniform_zero_loss_chain": (3 * beta0 < 3 * beta < 2 * a < u, True),
        "rho_domain": (0 < rho < 1, True),
        "finite_margin_domain": (0 < calculated["lambda_finite_uniform"]
                                 < calculated["lambda_critical_uniform"], True),
        "cutoff_constant": (144**2, 20736),
        "mahler_constant": (3 * 2**2, 12),
        "uniqueness_margin": (F(72, 144), F(1, 2)),
        "cost_envelope": (max(s, 2 * b), F(189, 100)),
        "cost_minus_upper_count": (2 * b - s, F(31, 9800)),
    }
    for record in records:
        if time.monotonic() - start >= protocol["budget"]["internal_seconds"]:
            record["status"] = "timeout"
            save()
            break
        key = record["id"]
        try:
            if key in calculated:
                actual, target = calculated[key], F(expected[key]["fraction"])
            else:
                actual, target = extra[key]
            widths = []
            for val in (actual, target):
                rational = F(val)
                widths.extend([abs(rational.numerator).bit_length(),
                               rational.denominator.bit_length()])
            record.update(actual=str(actual), expected=str(target), max_bits=max(widths))
            record["status"] = ("pass" if actual == target and
                max(widths) <= protocol["width"]["maximum_checked_integer_bits"] else "fail")
        except Exception as exc:
            record.update(status="error", error=type(exc).__name__ + ": " + str(exc))
        save()
    result["completed"] = all(r["status"] not in ("unstarted", "timeout") for r in records)
    save()
    print(json.dumps({"counts": result["status_counts"],
                      "elapsed_seconds": result["elapsed_seconds"]}))
    return 0 if all(r["status"] == "pass" for r in records) else 1


if __name__ == "__main__":
    raise SystemExit(main())
