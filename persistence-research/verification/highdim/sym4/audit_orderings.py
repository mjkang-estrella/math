"""Independently enumerate every distinct coefficient word in the assignment.

Each word specifies the coefficients on successively increasing positions. Its
inverse assigns those position ranks to the independent coefficient groups.
Replacing ranks by ANY increasing actual positions gives the same bijection.
"""
import sys
sys.dont_write_bytecode = True
import collections
import hashlib
import json
import math
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def words(counter, prefix=()):
    if not any(counter.values()):
        yield prefix
        return
    for c in sorted(counter):
        if counter[c]:
            counter[c] -= 1
            yield from words(counter, prefix + (c,))
            counter[c] += 1


def main():
    cfg = json.loads((HERE / 'assignment.json').read_text())['configurations']
    results = {}
    for key, rec in cfg.items():
        far = rec['far']
        counter = collections.Counter(far)
        expected = math.factorial(len(far)) // math.prod(math.factorial(n) for n in counter.values())
        seen = set()
        digest = hashlib.sha256()
        for word in words(counter.copy()):
            groups = tuple((c, tuple(i for i, d in enumerate(word) if d == c)) for c in sorted(counter))
            assert all(tuple(sorted(qs)) == qs and len(qs) == counter[c] for c, qs in groups)
            rebuilt = [None] * len(far)
            for c, qs in groups:
                for q in qs:
                    assert rebuilt[q] is None
                    rebuilt[q] = c
            assert tuple(rebuilt) == word and groups not in seen
            seen.add(groups)
            digest.update((','.join(map(str, word)) + '\n').encode())
        assert len(seen) == expected
        results[key] = {'result': 'PASS', 'distinct_orderings': expected, 'coefficient_words_sha256': digest.hexdigest()}
    out = {'result': 'PASS', 'configurations': results, 'total_distinct_orderings': sum(r['distinct_orderings'] for r in results.values())}
    (HERE / 'ordering_audit.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps({'result': 'PASS', 'configurations': len(results), 'total_distinct_orderings': out['total_distinct_orderings']}))


if __name__ == '__main__':
    main()
