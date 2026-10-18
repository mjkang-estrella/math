#!/usr/bin/env python3
# Copyright2026 Myeongjin Kang. MIT.
"""Authenticate adopted gate and explicit public inputs; no acceptance decision."""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from bundle_common import parse,read,require,verify_inputs
HERE=Path(__file__).absolute().parent
ROOT=HERE if (HERE/'frontier').is_dir() else HERE.parents[3]
def main():
    prep=parse(read(HERE,'preparation.json'));gate=parse(read(HERE,'FINAL-GATE.json'))
    require(prep['status']=='READY_LOCAL_ASSEMBLY_PARENT_ADOPTED','preparation status changed')
    expected=dict(prep);expected['status']='ALL_REVIEW_GATES_PASS';expected['full_scope']=gate['full_scope']
    require(expected==gate,'preparation/gate mismatch')
    count=verify_inputs(lambda name:read(ROOT,name),parse(read(HERE,'payload-selection.json')),gate)
    print('RELEASE INPUT IDENTITIES VERIFIED:',count,'selected research/evidence files; no acceptance')
if __name__=='__main__':
    try:main()
    except (OSError,ValueError,KeyError,TypeError,StopIteration) as e:sys.exit('RELEASE INPUTS REFUSED: '+str(e))
