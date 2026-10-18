# Integrity protocol

Code MIT, reused from analyticr45/r44 with the primary receipt list
adapted to this packet. This is infrastructure, not mathematical evidence.

An external SHA256 anchor is required:

    python -B verify.py --anchor EXTERNAL_SHA256
    python -B controls.py --anchor EXTERNAL_SHA256

The root `manifest.json` authenticates exact directory membership and all
other files, including private source bodies and nested files named
manifest.json. Every entry is checked with lstat; root/payload symlinks,
nonregular objects and hardlinked files are rejected. The verifier also
rechecks canonical source Git blobs/SHA256, the primary PDF/text extraction
and the finite algebra diagnostic. The manifest itself must be regular
and single-linked, and its digest must equal the supplied external anchor.

Controls make independent temporary copies inside this owned directory,
then remove them. They include positive/original-after-cleanup and copied
positive cases, wrong anchor, changed/missing/extra payload, extra empty
directory, nested manifest name, root/payload symlink, hardlink and FIFO.
Control output and the final anchor are delivered outside the packet to
avoid a circular self-authentication claim. No controls alter sealed prior
packets. The root manifest alone is omitted from its own payload inventory.

`private/` is ignored by the local .gitignore and contains all third-party
bodies. Public proof/provenance files are original explanatory material,
not manuscript-body reproductions. Parent alone integrates any packet.
