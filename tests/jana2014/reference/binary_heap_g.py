"""Reversible binary min-heap: six extract-mins, then five re-inserts.

The heap is the textbook one (CLRS MIN-HEAPIFY, sift-up on insert). Two
conventions are fixed by the program rather than by the algorithm and are
transcribed here as constants, the way the inputs are: the array is 1-indexed
with A[0] unused, and extract-min parks an "infinity" sentinel at the root
before swapping it to the end, so the vacated slots keep it instead of a zero.
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

KEYS = [1, 2, 3, 7, 4, 8, 9]
CELLS = 8
SENTINEL = 1000000
#: main extracts six minima, then re-inserts the 3rd, 2nd, 5th, 4th and 1st.
REINSERT_ORDER = [2, 1, 4, 3, 0]


def heapify(heap, size, i):
  left, right, smallest = 2 * i, 2 * i + 1, i
  if left <= size and heap[left] < heap[i]:
    smallest = left
  if right <= size and heap[right] < heap[smallest]:
    smallest = right
  if smallest != i:
    heap[i], heap[smallest] = heap[smallest], heap[i]
    heapify(heap, size, smallest)


def extract_min(heap, size):
  smallest = heap[1]
  heap[1] = SENTINEL
  heap[1], heap[size] = heap[size], heap[1]
  size -= 1
  heapify(heap, size, 1)
  return smallest, size


def insert(heap, size, key):
  size += 1
  i = size
  heap[i] = key
  while i > 1 and heap[i // 2] > heap[i]:
    heap[i], heap[i // 2] = heap[i // 2], heap[i]
    i //= 2
  return size


def expected():
  heap = [0] * CELLS
  for i, key in enumerate(KEYS, start=1):
    heap[i] = key
  size = len(KEYS)

  minima = []
  for _ in range(len(REINSERT_ORDER) + 1):
    smallest, size = extract_min(heap, size)
    minima.append(smallest)
  for index in REINSERT_ORDER:
    size = insert(heap, size, minima[index])

  result = {f"min{i + 1}": value for i, value in enumerate(minima)}
  result.update({"A": heap, "heapsize": size})
  return result
