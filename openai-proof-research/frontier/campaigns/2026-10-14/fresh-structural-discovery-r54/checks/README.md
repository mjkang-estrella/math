Checks are author-side only. exact_examples.py checks listed finite metric
examples, not universal routing upper bounds. integrity_controls.py is copied
and adapted from r53;13 disposable-copy controls reject wrong anchors,
changed/missing/extra files, extra directories, symlinks, hardlinks, FIFO and
nested manifests. seal.py inventories final bytes; the parent must supply
the externally communicated manifest hash. Private PDFs can be independently
re-extracted with pdftotext -layout; primary-extractions.json records replay.

An initial copied positive control correctly failed because shell output
redirection introduced a result file after the intermediate inventory was
created. The result slot was included in the intermediate inventory and the
full13 controls then passed; final inventory is resealed after results.
