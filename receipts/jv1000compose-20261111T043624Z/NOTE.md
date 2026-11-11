# NOTE — aborted attempt, kept rather than retracted

This receipt directory is an **author-aborted** run, not evidence about the committed code.
It was started while the round's Lean source was still being edited (docstring corrections and
two linter-warning cleanups landed after it began), then killed so the receipt of record could
be regenerated against the final source.

* `043624Z` — `STATUS: FAIL build_exit=-9 host_kill=True`.  The `-9` is **the author's own
  `kill`**, not a host OOM kill; the runner's heuristic cannot tell the two apart, so it is
  stated here.  The source it compiled is not the committed source.
* `044221Z` — killed mid-run; no `STATUS` was written.

The receipt of record is `jv1000compose-20261111T043857Z` (DONE, 35 banners, house triple,
plus a genuine from-scratch double compile recorded in its `NOTE.md`).
