# Family178 technical screen

Read screen.md for the precise logarithmic-girth retention deduction and why it is technical. No frozen candidate, contribution verdict, acceptance or count change is claimed. reading-and-provenance.md states actual read limits; all third-party inputs are private.

Verify using a detached seal hash supplied outside this directory:

    python verify.py --seal-sha256 EXPECTED_HASH

The read-only verifier authenticates exact file/directory membership, every payload, pinned Git blobs, private primary receipts and exact scalar arithmetic. It checks integrity and scalar bookkeeping, not the universal graph lemma or a contribution verdict. No network, compiler or package installation is needed. A wrong seal hash must fail. Do not substitute a hash computed from the same potentially untrusted packet for the external anchor.

Author: Myeongjin Kang; no affiliation. Original prose CC BY4.0; original code MIT; third-party rights unchanged. No publication authorized by this packet.
