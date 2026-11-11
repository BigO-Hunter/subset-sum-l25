# This receipt's axiom banner was killed by the host, not by the banner

`STATUS` in this directory reads `FAIL axiom gate: axiom banner exited -9`.  That is
the honest record of what happened, and this note says exactly what it does and does
not mean.  Nothing here is being retracted or overwritten.

## What the -9 is

`axioms.exit = -9` is SIGKILL on the `lake env lean KapilaRowAxioms.lean` process.
At the time of the run the host was at load average 66–116 (several other proof lanes
on the same volume), and the elapsed wall time of the banner step was long.  The
build itself succeeded in the same window:

| step | result |
|---|---|
| gate | `swapouts_delta60=0 free_pct=64` — PROCEED on the first iteration |
| lock | **DEVIATION**: bounded 240 s wait expired, `acquired=False`, build proceeded UNLOCKED |
| build | `build_exit = 0` in **4.1 s** — a *replay*: the oleans were already current |
| banner | `axioms_exit = -9` (SIGKILL), so the gate could not pass |
| oleans | recorded; `KapilaCmpSegStride.olean` 355 352 B sha256 `3943edfa…ed2859` |

## The compile evidence this receipt *does* carry

`build_seconds = 4.1` means lake rebuilt nothing: the named oleans in `oleans.txt` are
the ones produced by this round's **determinism double-compile**, run before this
receipt against the same sources:

* `KapilaCmpSegStride.olean` deleted and rebuilt **twice from scratch**, 40 s and 33 s,
  both to sha256 `3943edfa2798acc5274aa44295978e10732dd584bbdf23dcd81539f4b2ed2859`,
  355 352 bytes — the same hash `oleans.txt` records here.

So the receipt's 4.1 s is not cited as compile evidence; the double-compile is, and
this receipt confirms the bytes.

## The banner, run independently on the same oleans

`axioms.independent.txt` in this directory is a separate foreground run of the
identical command on the identical oleans:

```
lake env lean KapilaRowAxioms.lean      → exit 0
```

* **266** `depends on axioms` lines
* 151 `[propext, Classical.choice, Quot.sound]`, 68 `[propext, Quot.sound]`, 47 `[propext]`
* **two** declarations on no axioms at all (`digitwise_is_wide_at_digit`,
  `cmpSegReload_couples_roles`) — both definitional equations
* no `sorryAx`, no `native_decide`, no `Lean.ofReduceBool`
* `Statement.lean` unchanged: sha256 `3dc6567e…34aa`

It is labelled *independent* because it is **not** the runner's own banner: the
runner's attempt is the one that died.  A reader who requires the runner's own banner
must not accept this file as that; the honest statement is "the banner was proved to
pass out-of-band, the runner's copy was SIGKILLed".

## Whose head

`head.sha` = `a40f5419…68cb` — the **peer jv1000 lane's** commit, which landed in this
shared worktree during the receipt.  This round's own commit stacks on it.  That
commit also swept this round's `PROGRESS.md` entry into itself (the shared-index
hazard: one file, two authors, one `git add`); the content is intact and attributed
here rather than in the commit message it landed under.
