"""Exercise actual hash-protected certificate reuse in a forked search worker."""
import sys
sys.dont_write_bytecode = True
import concurrent.futures
import json
import multiprocessing
import pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import continue_sym2 as continuation


def main():
    continuation.library()
    key = '14112:136|45,45,54'
    rec = continuation.read(continuation.HERE / 'assignment.json')['configurations'][key]
    args = (key, rec, 10, 1000000, (2, 3, 7), 'cache_control', 0, 3, True, 96, 400, False, False)
    with concurrent.futures.ProcessPoolExecutor(max_workers=1, mp_context=multiprocessing.get_context('fork')) as pool:
        result = pool.submit(continuation.search_worker, args).result()
    assert result['status'] == 'COMPLETE_PENDING_CHECKS'
    assert len(result['jobs']) == 1 and all(job.get('cached') for job in result['jobs'])
    out = {'result': 'PASS', 'context': 'fork', 'inherited_domains': len(continuation.LIBRARY), 'search_result': result}
    continuation.save(continuation.HERE / 'cache_test_results.json', out)
    print(json.dumps({'result': 'PASS', 'context': 'fork', 'inherited_domains': len(continuation.LIBRARY)}))


if __name__ == '__main__':
    main()
