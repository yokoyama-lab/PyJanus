"""Reversible binary min-heap: six extract-mins, then five re-inserts.

Only the extracted minima and the resulting size are asserted. The final array
layout depends on this encoding's sift order, and the per-operation garbage
arrays are garbage by construction, so neither belongs to the algorithm.
"""

GARBAGE = [
  "heapgarbage",
  "heapgarbage1",
  "heapgarbage2",
  "heapgarbage3",
  "heapgarbage4",
  "heapgarbage5",
  "insertgarbage",
  "insertgarbage1",
  "insertgarbage2",
  "insertgarbage3",
  "insertgarbage4",
  "insertcounter",
  "insertcounter1",
  "insertcounter2",
  "insertcounter3",
  "insertcounter4",
]

PARTIAL = "the final array layout, which depends on this encoding's sift order"

KEYS = [1, 2, 3, 7, 4, 8, 9]
EXTRACTS = 6
REINSERTS = 5


def expected():
  minima = sorted(KEYS)[:EXTRACTS]
  result = {f"min{i + 1}": value for i, value in enumerate(minima)}
  result["heapsize"] = len(KEYS) - EXTRACTS + REINSERTS
  return result
