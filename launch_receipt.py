#!/usr/bin/env python3
"""Launch the bounded receipt runner detached (the gate alone can exceed the 250 s
shell watchdog; the runner must survive the wrapper's death to leave a receipt)."""
import subprocess

p = subprocess.Popen(
    ["/usr/bin/python3", "/Volumes/Substrate-1/bigo/kapila-row-lane/kapila_receipts_bounded.py"],
    cwd="/Volumes/Substrate-1/bigo/kapila-row-lane",
    start_new_session=True,
    stdout=open("/tmp/kapila_leancheck/receipt.log", "a"),
    stderr=subprocess.STDOUT,
)
print("launched receipt runner pid", p.pid)
