#!/bin/bash
# Wrapper: detach receipts_run.py (Python holds the flock for the full run).
exec /usr/bin/env python3 /Volumes/Substrate-1/bigo/o1-lane/receipts_run.py
