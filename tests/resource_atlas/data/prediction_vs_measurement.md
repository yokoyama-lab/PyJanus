# Prediction vs measurement

## corpus (101 programs, 101 measured)

### 1. call_depth_peak <= H (H = longest path in an acyclic call graph)

| | count |
|---|---:|
| acyclic call graph (bound H exists) | 84 |
| cyclic call graph (no bound) | 17 |
| bound holds (measured <= H) | 84 |
| **violations** (measured > H) | 0 |
| bound tight (measured = H) | 84 / 84 |
| slack values H - measured | 0 |

Cyclic programs measured call_depth_peak in [4, 7].

### 2. stack_peak = 0 certificate (no push/pop reachable from main)

| | count |
|---|---:|
| certified stack-free | 68 |
| certified and measured 0 | 68 |
| **violations** (certified but measured > 0) | 0 |
| not certified (push/pop reachable) | 33 |
| not certified but measured 0 (imprecision, not unsoundness) | 0 |
| measured stack_peak > 0 | 33 |

### 3. total_calls <= C (acyclic and no call inside a loop body)

| | count |
|---|---:|
| bound C exists | 63 |
| bound holds | 63 |
| **violations** | 0 |
| bound tight (measured = C) | 63 / 63 |
| no bound: call inside a loop | 27 |
| no bound: recursion | 17 |

## generated (130 programs, 130 measured)

### 1. call_depth_peak <= H (H = longest path in an acyclic call graph)

| | count |
|---|---:|
| acyclic call graph (bound H exists) | 130 |
| cyclic call graph (no bound) | 0 |
| bound holds (measured <= H) | 130 |
| **violations** (measured > H) | 0 |
| bound tight (measured = H) | 130 / 130 |
| slack values H - measured | 0 |

### 2. stack_peak = 0 certificate (no push/pop reachable from main)

| | count |
|---|---:|
| certified stack-free | 60 |
| certified and measured 0 | 60 |
| **violations** (certified but measured > 0) | 0 |
| not certified (push/pop reachable) | 70 |
| not certified but measured 0 (imprecision, not unsoundness) | 0 |
| measured stack_peak > 0 | 70 |

### 3. total_calls <= C (acyclic and no call inside a loop body)

| | count |
|---|---:|
| bound C exists | 130 |
| bound holds | 130 |
| **violations** | 0 |
| bound tight (measured = C) | 130 / 130 |
| no bound: call inside a loop | 0 |
| no bound: recursion | 0 |

## Violations

None: every measurement is within its static bound.
