"""Frozen W006 candidate. Input: N,L only; no evaluator data or factor oracle."""
import json
import math
import time
import tracemalloc


def emit(kind, data):
    print(json.dumps({"kind": kind, "data": data}, separators=(",", ":")), flush=True)


class Cap(Exception):
    pass


def candidate(N, L):
    started = time.perf_counter()
    rec = {"N": N, "L": L, "status": "UNKNOWN", "factor": None,
           "multiply_adds": 0, "convolutions": 0, "steps": [],
           "residues": None, "gcds": [], "max_reduced_operand_bits": N.bit_length(),
           "max_arithmetic_operand_bits": N.bit_length(), "stop_reason": None}

    def check():
        if time.perf_counter() - started >= 1.0:
            raise Cap("candidate_time")
        if tracemalloc.get_traced_memory()[1] > 32 * 1024 * 1024:
            raise Cap("traced_allocation")

    def multiply(a, b):
        out = [0] * L
        for i in range(L):
            for j in range(L):
                check()
                if rec["multiply_adds"] >= 20000:
                    raise Cap("multiply_adds")
                k = (i + j) % L
                product = a[i] * b[j]
                total = out[k] + product
                out[k] = total % N
                rec["multiply_adds"] += 1
                rec["max_reduced_operand_bits"] = max(
                    rec["max_reduced_operand_bits"], a[i].bit_length(),
                    b[j].bit_length(), out[k].bit_length())
                rec["max_arithmetic_operand_bits"] = max(
                    rec["max_arithmetic_operand_bits"], product.bit_length(),
                    total.bit_length())
        rec["convolutions"] += 1
        return out

    try:
        a = [1] + [0] * (L - 1)
        b = [1, 1] + [0] * (L - 2)
        exponent = N - 1
        while exponent:
            check()
            old = exponent
            if exponent & 1:
                a = multiply(a, b)
            exponent >>= 1
            if exponent:
                b = multiply(b, b)
            step = {"exponent_before": old, "exponent_after": exponent,
                    "accumulator_multiplied": bool(old & 1),
                    "base_squared": bool(exponent),
                    "multiply_adds": rec["multiply_adds"]}
            rec["steps"].append(step)
            emit("step", step)
        rec["residues"] = a
        emit("residues", a)
        for index, value in enumerate(a):
            check()
            d = math.gcd(value, N)
            rec["gcds"].append(d)
            emit("gcd", {"index": index, "residue": value, "gcd": d})
            if 1 < d < N:
                if N % d:
                    raise ArithmeticError("invalid factor")
                if rec["factor"] is None:
                    rec["factor"] = d
        check()
        rec["status"] = "FACTOR" if rec["factor"] is not None else "NO_FACTOR"
        rec["stop_reason"] = "completed_all_gcds"
    except Cap as exc:
        rec["status"] = "UNKNOWN"
        rec["factor"] = None
        rec["stop_reason"] = str(exc)
    except Exception as exc:
        rec["status"] = "UNKNOWN"
        rec["factor"] = None
        rec["stop_reason"] = "exception: " + repr(exc)
    rec["elapsed_seconds"] = time.perf_counter() - started
    rec["traced_current_bytes"], rec["traced_peak_bytes"] = tracemalloc.get_traced_memory()
    emit("candidate", rec)
    return rec
