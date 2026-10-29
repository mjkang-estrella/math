# Preserved failures and limits

- 20:10:44–45 UTC, GitHub REST HEAD requests for Omega and OpenAI each returned HTTP403 rate limit exceeded. No retries or alternate-head bypass. The supplied last-known heads are not certified live current by this lane.
- Evidence Press local-stability page returned HTTP403 Forbidden at20:12:42 UTC. No retry/bypass. Search discovery metadata is not an actual proof-body reading; successor-body gap retained.
- Initial guarded read.py failed ModuleNotFoundError: bs4. Initial script preserved as initial-read.py; no source parsing was completed by it. Replaced using standard-library HTMLParser under identical guard; passed. Initial process exit1, sampledRSS30265344, wall0.1202s. No cap increases.
- Corpus scan passed at120342 files, RSS330235904, wall83.8226s. It streams every file's hash and uses bounded overlapping chunks; no read_bytes aggregate. Regex explicitly self-checks literal2605.02023.
- HTTP downloads are capped at18MB; no download hit the cap. Public-source discovery is bounded, not an exhaustive literature/priority clearance.
