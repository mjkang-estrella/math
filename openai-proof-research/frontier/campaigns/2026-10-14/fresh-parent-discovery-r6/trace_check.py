#!/usr/bin/env python3
"""Replay two specified source-certificate paths and check their strong-game races.

MIT; original wrapper by Myeongjin Kang. The private source evaluator is an
unmodified pinned upstream input, not original code. This does not audit the
upstream weak-win theorem or solve the full strong game.
"""
import hashlib
import importlib.util
import json
import sys
from functools import lru_cache
from pathlib import Path

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parent
SOURCE = BASE / "private/verification/supporting/route21"
spec = importlib.util.spec_from_file_location("pinned_snaky", SOURCE / "independent.py")
q = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = q
spec.loader.exec_module(q)
raw = (SOURCE / "certificate.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest() == q.DATA_SHA256
cert = q.Certificate(raw.decode("ascii"))


@lru_cache(None)
def value(tree):
    if isinstance(tree, q.Reference):
        return q.transform(cert.cards[tree.card], tree.symmetry, tree.shift)
    children = [value(child) for child in tree.children]
    support = frozenset({tree.pivot}).union(*(c.support for c in children))
    required = (frozenset().union(*(c.required for c in children)) |
                frozenset.intersection(*(c.support for c in children))) - {tree.pivot}
    return q.Value(required, support, 1 + max(c.height for c in children))


def compose(outer, inner):
    s, a = outer
    r, b = inner
    m, n = q.MATRICES[s], q.MATRICES[r]
    product = tuple(tuple(sum(m[i][k] * n[k][j] for k in range(2))
                          for j in range(2)) for i in range(2))
    return q.MATRICES.index(product), q.transform_point(b, s, a)


def placed(points, frame):
    return frozenset(q.transform_point(p, *frame) for p in points)


def target_in(owned):
    """All eight orientations, every translation that could lie in owned."""
    if len(owned) < 6:
        return None
    for symmetry in range(8):
        shape = [q.transform_point(p, symmetry, (0, 0)) for p in q.SNAKE]
        for anchor in sorted(owned):
            shift = (anchor[0] - shape[0][0], anchor[1] - shape[0][1])
            candidate = frozenset((p[0] + shift[0], p[1] + shift[1]) for p in shape)
            if candidate <= owned:
                return sorted(candidate)
    return None


REMOTE = [(100 + x, 100 + y) for x, y in q.SNAKE]


def replay(alternative=False):
    tree = cert.expressions[727]
    frame = (0, (0, 0))
    maker, breaker, rows = frozenset(), frozenset(), []
    for turn in range(1, 8):
        if isinstance(tree, q.Reference):
            frame = compose(frame, (tree.symmetry, tree.shift))
            if tree.card < 6:
                missing = placed(q.SNAKE, frame) - maker
                assert len(missing) == 1
                move = next(iter(missing))
                assert move not in breaker
                maker |= {move}
                assert target_in(maker)
                rows.append({"turn": turn, "maker": move, "maker_target": target_in(maker)})
                return rows
            tree = cert.expressions[tree.card]
        v = value(tree)
        assert placed(v.required, frame) <= maker
        assert not placed(v.support, frame) & breaker
        move = q.transform_point(tree.pivot, *frame)
        assert move not in maker | breaker  # neither replay requires a replacement
        maker |= {move}
        row = {"turn": turn, "maker": move, "maker_target": target_in(maker)}
        if row["maker_target"]:
            rows.append(row)
            return rows
        reply = REMOTE[turn - 1]
        assert reply not in maker | breaker
        breaker |= {reply}
        row.update(breaker=reply, breaker_target=target_in(breaker))
        if row["breaker_target"]:
            rows.append(row)
            return rows
        survivors = [child for child in tree.children
                     if reply not in placed(value(child).support, frame)]
        child = survivors[0]
        if alternative and turn == 4:
            child = q.Reference(115, 2, (4, 0))
            assert child in survivors
        row["child"] = {"card": child.card, "symmetry": child.symmetry,
                        "shift": child.shift}
        rows.append(row)
        tree = child
    raise AssertionError("specified path did not terminate")


def main():
    printed = replay()
    alternate = replay(True)
    assert [r["maker"] for r in printed] == [(8, 8), (8, 7), (8, 9), (8, 10), (8, 11), (9, 11)]
    assert printed[-1]["turn"] == 6 and printed[-1]["breaker_target"]
    assert not any(r["maker_target"] for r in printed)
    assert [r["maker"] for r in alternate] == [(8, 8), (8, 7), (8, 9), (8, 10), (7, 7), (7, 6)]
    assert alternate[-1]["turn"] == 6 and alternate[-1]["maker_target"]
    print(json.dumps({"status": "TWO_PATHS_CHECKED_NOT_FULL_STRONG_GAME",
                      "certificate_sha256": q.DATA_SHA256,
                      "printed_policy": printed, "alternate_path": alternate},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
