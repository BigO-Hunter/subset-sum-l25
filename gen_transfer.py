#!/usr/bin/env python3
"""Generate §C10 — the `getD`-agreement transfer, mechanically.

The seam round 16 named: `cmpSeg_reaches` is stated on `cmpSeg cont`, but the program
that *runs* is `cmpSeg 29 ++ tail` (`cmpSegmentProgram`), which differs from it at
position 29 — exactly where the segment's last step jumps.  Closing it does not mean
re-deriving the segment; it means replaying §C4–§C6's chain for an abstract `P` that
agrees with `cmpSeg 29` on `0…28`.  Every proof in that chain is program-independent
except for two things:

  * the `getD` facts (`have dNN : (cmpSeg cont).getD NN = INSTR := rfl`) — which
    become `P.getD NN = INSTR` by the agreement hypothesis `hgd`; and
  * the word `cont` in the `exec` statements — which becomes `29`, because `29` is
    the position the abstract program is *run into*.

So the transformation is textual and total, and this script is the receipt that it is
textual and total: it reads §C4–§C6 out of the module, applies the six rewrites below
to every declaration that names `(cmpSeg cont)`, and emits a `_gen` copy of each.
Nothing is re-argued; if a declaration does not contain `(cmpSeg cont)` it is not
copied.

Rewrites, in order (order matters: `(cmpSeg cont)` must go before the bare `cont`,
and the getD rewrite must come after both):

  R1  rename every declaration and every reference: `cmpSeg_X` -> `cmpSeg_X_gen`
  R2  `(cont := cont)` -> ``                        (call sites)
  R3  `{cont : Nat} ` -> ``                         (binders)
  R4  `(cmpSeg cont)` -> `P`                        (statements and getD facts)
  R5  `\\bcont\\b` -> `29`                           (the exit position)
  R6  `have dNN : P.getD NN Instr.reject = I := rfl`
        -> `... := by rw [hgd NN (by omega)]; rfl`
  R7  insert `{P : List Instr} (hgd : ...)` after the declaration's name, and
      `(hgd := hgd)` after the name at every call site.
"""
import re
import sys
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/kapila-row-lane")
SRC = LANE / "SubsetSumL25/Row/KapilaCmpSeg.lean"

NAMES = [
    "cmpSeg_walk_eq_step", "cmpSeg_walk_eq_term", "cmpSeg_walk_head",
    "cmpSeg_walk_lt", "cmpSeg_walk_gt", "cmpSeg_walk",
    "cmpSeg_head", "cmpSeg_above", "cmpSeg_miss", "cmpSeg_below",
    "cmpSeg_tieV_zero", "cmpSeg_tieA_zero", "cmpSeg_tieV", "cmpSeg_tieA",
    "cmpSeg_reaches_bound", "cmpSeg_reaches",
]
# longest first so `cmpSeg_walk_eq_step` wins over `cmpSeg_walk`
ORDERED = sorted(NAMES, key=len, reverse=True)

HGD = ("(hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject)")


def rename_names(text):
    """R1 — append `_gen` to every occurrence of every transformed name."""
    for n in ORDERED:
        text = re.sub(r"\b" + n + r"\b(?!_gen)", n + "_gen", text)
    return text


def transform_decl(block):
    body = block
    # R1
    body = rename_names(body)
    # R2: drop the `(cont := cont)` arguments
    body = body.replace("(cont := cont) ", "")
    body = body.replace("(cont := cont)", "")
    # R3: drop the `{cont : Nat}` binder
    body = body.replace("{cont : Nat} ", "")
    body = body.replace("{cont : Nat}", "")
    # R4
    body = body.replace("(cmpSeg cont)", "P")
    # R5
    body = re.sub(r"\bcont\b", "29", body)
    # R6: the getD facts become applications of hgd
    def r6(m):
        return (m.group(1) + m.group(2) + m.group(3)
                + " := by rw [hgd " + m.group(2) + " (by omega)]; rfl")
    body = re.sub(
        r"(have d\d+ : P\.getD )(\d+)( Instr\.reject = .*?)( := rfl)", r6, body)
    # R7b': the one positional call site (`cmpSeg_reaches_bound`'s) gains hgd first
    body = body.replace("cmpSeg_reaches_gen hfitH", "cmpSeg_reaches_gen hgd hfitH")
    # R7a: the declaration's own name gains the P binder and hgd
    body = re.sub(r"(theorem cmpSeg_\w+_gen )", r"\1{P : List Instr} " + HGD + " ", body, count=1)
    # R7b: call sites gain `(hgd := hgd)`
    for n in ORDERED:
        body = body.replace(n + "_gen (", n + "_gen (hgd := hgd) (")
    # the declaration line itself must not carry the call-site form
    body = re.sub(r"(theorem cmpSeg_\w+_gen \{P : List Instr\} \(hgd := hgd\) \(hgd : )",
                  r"\1", body)
    return body


def main():
    text = SRC.read_text()
    start = text.index("/-! ### §C4 — the low walk")
    end = text.index("/-! ### §C7 — the composition state")
    region = text[start:end]

    # split into blocks, each beginning at a `theorem` line, keeping what follows
    idx = [m.start() for m in re.finditer(r"(?m)^theorem ", region)]
    blocks = []
    for i, s in enumerate(idx):
        e = idx[i + 1] if i + 1 < len(idx) else len(region)
        blocks.append((s, e, region[s:e]))

    out_blocks = []
    for s, e, blk in blocks:
        name = re.match(r"theorem (\w+)", blk).group(1)
        if "(cmpSeg cont)" not in blk:
            print(f"  skip  {name}   (no (cmpSeg cont))")
            continue
        # stop at the next docstring that belongs to the NEXT declaration
        cut = blk.find("\n/-! ")
        if cut == -1:
            cut = blk.find("\n/-- **", 1)
        decl = blk if cut == -1 else blk[:cut]
        out_blocks.append((name, transform_decl(decl)))
        print(f"  copy  {name} -> {name}_gen   ({len(decl.splitlines())} lines)")

    header = '''/-! ### §C10 — THE TRANSFER: §C4–§C6 replayed for an abstract program `P`

§C9 left one seam open and said so: `cmpSeg_reaches` is stated on `cmpSeg cont`, the
program that runs is `cmpSegmentProgram tail = cmpSeg 29 ++ tail`, and the two differ
at position `29` — precisely where the segment's last step jumps.  Comparing the two
`exec` chains therefore cannot be a congruence: at `29` the plain program reads
`Instr.reject` (the `getD` fallback) and the composed one reads the tail.

What *is* true — and is all the loop needs — is that a program agreeing with
`cmpSeg 29` on positions `0…28` walks the identical trace below `29`, so the segment's
whole chain replays against it.  Simulation first, as always: `sim_loop.py` arm A
records the two traces step for step over six digit blocks and finds them equal in pc
*and* memory up to the arrival at `29`, and equal there too; only the instruction
`getD 29` differs, and that difference is the composition, not a defect.

The declarations below are that replay, and they are mechanically generated from
§C4–§C6 by `gen_transfer.py` (the six rewrites are listed in its docstring; the script
prints which declarations it copied and which it skipped).  No step is re-argued: the
only things that change are the `getD` facts — `rfl` becomes `hgd` — and the word
`cont`, which becomes `29`, the position the abstract program is run into.  The
`_gen` suffix is deliberate: the free-`cont` originals stay exactly as they were, so
nothing here can break them.

`cmpSeg_reaches_program` is the only instantiation the loop uses.
-/

'''

    footer = '''
/-- **THE ADJUDICATED ENTRY REACH, ON THE REAL PROGRAM.**  Instantiate §C10's
chain at `P := cmpSegmentProgram tail`, whose agreement hypothesis is exactly
`cmpSegment_getD`.  This is the statement §C9 could not make: the segment's own run,
from position `0` of the *composed* program, reaches position `29` in exactly
`cmpSegCost` steps with the verdict in cell `6` and the frame intact — the same
state-level conclusion as `cmpSeg_reaches`, but on the bytes that actually execute. -/
theorem cmpSeg_reaches_program (tail : List Instr) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h9 : h 9 = 2 ^ r)
    (k0 : st 0 = addrV + p) (k1 : st 1 = addrA + p) (k2 : st 2 = p)
    (hadA : h (addrA + p) + 2 ^ r < 2 ^ w)
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w)
    (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSegmentProgram tail) ρ (S + cmpSegCost h addrV addrA p r) 0 0 (memOf w st)
        = exec (cmpSegmentProgram tail) ρ S 29 0 (memOf w st') :=
  cmpSeg_reaches_gen (fun i hi => cmpSegment_getD tail hi) hfitH hV hA h7 h8 h9 k0 k1 k2 hadA hadV hag hfit S
'''

    gen = header + "\n".join(b for _, b in out_blocks) + footer
    target = LANE / "parts/c10_transfer_gen.lean"
    target.write_text(gen)
    print(f"\nwrote {target}  ({len(gen.splitlines())} lines)")


if __name__ == "__main__":
    main()
