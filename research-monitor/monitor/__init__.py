"""Read-only live monitor for the dlp-research repository.

Nothing in this package writes to the research tree. All repository access
goes through `sources` (allowlisted text files) and `gitinfo` (fixed git
subcommands with timeouts and output caps).
"""
