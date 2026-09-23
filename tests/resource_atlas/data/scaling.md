# Scaling table (RC-03 §規模を振った計測, re-measured with ~20 sizes per family)

`steps_ratio` = steps(size) / steps(previous size) (the adjacent ratio rc03 reports;
no curve fitting).  `match` = measured stack_peak equals the predicted law.

## gcd_fib

Predicted law: stack_peak = k (number of subtractions; a=F(k+2), b=F(k+1))

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 1 | a=F(3)=2 b=F(2)=1 | 8 |  | 1 | 1 | True | 1 | 1 | 3 |
| 2 | a=F(4)=3 b=F(3)=2 | 12 | 1.500 | 2 | 2 | True | 1 | 1 | 3 |
| 3 | a=F(5)=5 b=F(4)=3 | 16 | 1.333 | 3 | 3 | True | 1 | 1 | 4 |
| 4 | a=F(6)=8 b=F(5)=5 | 20 | 1.250 | 4 | 4 | True | 1 | 1 | 4 |
| 5 | a=F(7)=13 b=F(6)=8 | 24 | 1.200 | 5 | 5 | True | 1 | 1 | 5 |
| 6 | a=F(8)=21 b=F(7)=13 | 28 | 1.167 | 6 | 6 | True | 1 | 1 | 5 |
| 7 | a=F(9)=34 b=F(8)=21 | 32 | 1.143 | 7 | 7 | True | 1 | 1 | 6 |
| 8 | a=F(10)=55 b=F(9)=34 | 36 | 1.125 | 8 | 8 | True | 1 | 1 | 6 |
| 9 | a=F(11)=89 b=F(10)=55 | 40 | 1.111 | 9 | 9 | True | 1 | 1 | 7 |
| 10 | a=F(12)=144 b=F(11)=89 | 44 | 1.100 | 10 | 10 | True | 1 | 1 | 7 |
| 11 | a=F(13)=233 b=F(12)=144 | 48 | 1.091 | 11 | 11 | True | 1 | 1 | 8 |
| 12 | a=F(14)=377 b=F(13)=233 | 52 | 1.083 | 12 | 12 | True | 1 | 1 | 8 |
| 13 | a=F(15)=610 b=F(14)=377 | 56 | 1.077 | 13 | 13 | True | 1 | 1 | 9 |
| 14 | a=F(16)=987 b=F(15)=610 | 60 | 1.071 | 14 | 14 | True | 1 | 1 | 9 |
| 15 | a=F(17)=1597 b=F(16)=987 | 64 | 1.067 | 15 | 15 | True | 1 | 1 | 10 |
| 16 | a=F(18)=2584 b=F(17)=1597 | 68 | 1.062 | 16 | 16 | True | 1 | 1 | 10 |
| 17 | a=F(19)=4181 b=F(18)=2584 | 72 | 1.059 | 17 | 17 | True | 1 | 1 | 11 |
| 18 | a=F(20)=6765 b=F(19)=4181 | 76 | 1.056 | 18 | 18 | True | 1 | 1 | 11 |
| 19 | a=F(21)=10946 b=F(20)=6765 | 80 | 1.053 | 19 | 19 | True | 1 | 1 | 12 |
| 20 | a=F(22)=17711 b=F(21)=10946 | 84 | 1.050 | 20 | 20 | True | 1 | 1 | 12 |

20/20 points match the predicted stack_peak.

## gcd_pair

Predicted law: stack_peak = (sum of Euclid quotients) - 1

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 3 | a=48 b=36 sum_of_quotients=4 | 16 |  | 3 | 3 | True | 1 | 1 | 9 |
| 18 | a=100 b=7 sum_of_quotients=19 | 76 |  | 18 | 18 | True | 1 | 1 | 17 |
| 5 | a=60 b=25 sum_of_quotients=6 | 24 |  | 5 | 5 | True | 1 | 1 | 9 |
| 6 | a=17 b=5 sum_of_quotients=7 | 28 |  | 6 | 6 | True | 1 | 1 | 6 |
| 98 | a=99 b=1 sum_of_quotients=99 | 396 |  | 98 | 98 | True | 1 | 1 | 100 |
| 335 | a=1000 b=3 sum_of_quotients=336 | 1344 |  | 335 | 335 | True | 1 | 1 | 335 |

6/6 points match the predicted stack_peak.

## bubble_sort

Predicted law: stack_peak = n(n-1)/2 (reverse-sorted input; call + uncall as in the original)

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 2 | n=2 reverse-sorted | 39 |  | 1 | 1 | True | 1 | 2 | 12 |
| 3 | n=3 reverse-sorted | 79 | 2.026 | 3 | 3 | True | 1 | 2 | 19 |
| 4 | n=4 reverse-sorted | 135 | 1.709 | 6 | 6 | True | 1 | 2 | 28 |
| 5 | n=5 reverse-sorted | 207 | 1.533 | 10 | 10 | True | 1 | 2 | 37 |
| 6 | n=6 reverse-sorted | 295 | 1.425 | 15 | 15 | True | 1 | 2 | 46 |
| 7 | n=7 reverse-sorted | 399 | 1.353 | 21 | 21 | True | 1 | 2 | 56 |
| 8 | n=8 reverse-sorted | 519 | 1.301 | 28 | 28 | True | 1 | 2 | 67 |
| 9 | n=9 reverse-sorted | 655 | 1.262 | 36 | 36 | True | 1 | 2 | 78 |
| 10 | n=10 reverse-sorted | 807 | 1.232 | 45 | 45 | True | 1 | 2 | 89 |
| 11 | n=11 reverse-sorted | 975 | 1.208 | 55 | 55 | True | 1 | 2 | 100 |
| 12 | n=12 reverse-sorted | 1159 | 1.189 | 66 | 66 | True | 1 | 2 | 111 |
| 13 | n=13 reverse-sorted | 1359 | 1.173 | 78 | 78 | True | 1 | 2 | 123 |
| 14 | n=14 reverse-sorted | 1575 | 1.159 | 91 | 91 | True | 1 | 2 | 135 |
| 15 | n=15 reverse-sorted | 1807 | 1.147 | 105 | 105 | True | 1 | 2 | 147 |
| 16 | n=16 reverse-sorted | 2055 | 1.137 | 120 | 120 | True | 1 | 2 | 160 |
| 17 | n=17 reverse-sorted | 2319 | 1.128 | 136 | 136 | True | 1 | 2 | 173 |
| 18 | n=18 reverse-sorted | 2599 | 1.121 | 153 | 153 | True | 1 | 2 | 186 |
| 19 | n=19 reverse-sorted | 2895 | 1.114 | 171 | 171 | True | 1 | 2 | 199 |
| 20 | n=20 reverse-sorted | 3207 | 1.108 | 190 | 190 | True | 1 | 2 | 212 |
| 21 | n=21 reverse-sorted | 3535 | 1.102 | 210 | 210 | True | 1 | 2 | 225 |

20/20 points match the predicted stack_peak.

## bubble_sort_fwd

Predicted law: stack_peak = n(n-1)/2 (reverse-sorted input; forward call only)

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 2 | n=2 reverse-sorted, call only | 20 |  | 1 | 1 | True | 1 | 1 | 12 |
| 3 | n=3 reverse-sorted, call only | 40 | 2.000 | 3 | 3 | True | 1 | 1 | 19 |
| 4 | n=4 reverse-sorted, call only | 68 | 1.700 | 6 | 6 | True | 1 | 1 | 29 |
| 5 | n=5 reverse-sorted, call only | 104 | 1.529 | 10 | 10 | True | 1 | 1 | 39 |
| 6 | n=6 reverse-sorted, call only | 148 | 1.423 | 15 | 15 | True | 1 | 1 | 50 |
| 7 | n=7 reverse-sorted, call only | 200 | 1.351 | 21 | 21 | True | 1 | 1 | 63 |
| 8 | n=8 reverse-sorted, call only | 260 | 1.300 | 28 | 28 | True | 1 | 1 | 78 |
| 9 | n=9 reverse-sorted, call only | 328 | 1.262 | 36 | 36 | True | 1 | 1 | 93 |
| 10 | n=10 reverse-sorted, call only | 404 | 1.232 | 45 | 45 | True | 1 | 1 | 109 |
| 11 | n=11 reverse-sorted, call only | 488 | 1.208 | 55 | 55 | True | 1 | 1 | 126 |
| 12 | n=12 reverse-sorted, call only | 580 | 1.189 | 66 | 66 | True | 1 | 1 | 144 |
| 13 | n=13 reverse-sorted, call only | 680 | 1.172 | 78 | 78 | True | 1 | 1 | 164 |
| 14 | n=14 reverse-sorted, call only | 788 | 1.159 | 91 | 91 | True | 1 | 1 | 185 |
| 15 | n=15 reverse-sorted, call only | 904 | 1.147 | 105 | 105 | True | 1 | 1 | 207 |
| 16 | n=16 reverse-sorted, call only | 1028 | 1.137 | 120 | 120 | True | 1 | 1 | 231 |
| 17 | n=17 reverse-sorted, call only | 1160 | 1.128 | 136 | 136 | True | 1 | 1 | 255 |
| 18 | n=18 reverse-sorted, call only | 1300 | 1.121 | 153 | 153 | True | 1 | 1 | 280 |
| 19 | n=19 reverse-sorted, call only | 1448 | 1.114 | 171 | 171 | True | 1 | 1 | 306 |
| 20 | n=20 reverse-sorted, call only | 1604 | 1.108 | 190 | 190 | True | 1 | 1 | 333 |
| 21 | n=21 reverse-sorted, call only | 1768 | 1.102 | 210 | 210 | True | 1 | 1 | 361 |

20/20 points match the predicted stack_peak.

## bubble_sort_perm

Predicted law: stack_peak = n(n-1)/2 (pseudo-random permutation: input-order independent)

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 5 | n=5 pseudo-random permutation (seed 5) | 135 |  | 10 | 10 | True | 1 | 2 | 37 |
| 8 | n=8 pseudo-random permutation (seed 8) | 407 |  | 28 | 28 | True | 1 | 2 | 67 |
| 13 | n=13 pseudo-random permutation (seed 13) | 1023 |  | 78 | 78 | True | 1 | 2 | 123 |
| 21 | n=21 pseudo-random permutation (seed 21) | 2631 |  | 210 | 210 | True | 1 | 2 | 225 |

4/4 points match the predicted stack_peak.

## knapsack

Predicted law: stack_peak = 0 (bottom-up DP; cap = n+2)

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 1 | n=1 cap=3 | 24 |  | 0 | 0 | True | 1 | 1 | 11 |
| 2 | n=2 cap=4 | 50 | 2.083 | 0 | 0 | True | 1 | 1 | 28 |
| 3 | n=3 cap=5 | 83 | 1.660 | 0 | 0 | True | 1 | 1 | 50 |
| 4 | n=4 cap=6 | 123 | 1.482 | 0 | 0 | True | 1 | 1 | 81 |
| 5 | n=5 cap=7 | 170 | 1.382 | 0 | 0 | True | 1 | 1 | 119 |
| 6 | n=6 cap=8 | 224 | 1.318 | 0 | 0 | True | 1 | 1 | 167 |
| 7 | n=7 cap=9 | 285 | 1.272 | 0 | 0 | True | 1 | 1 | 223 |
| 8 | n=8 cap=10 | 353 | 1.239 | 0 | 0 | True | 1 | 1 | 288 |
| 9 | n=9 cap=11 | 428 | 1.212 | 0 | 0 | True | 1 | 1 | 360 |
| 10 | n=10 cap=12 | 510 | 1.192 | 0 | 0 | True | 1 | 1 | 440 |
| 11 | n=11 cap=13 | 599 | 1.175 | 0 | 0 | True | 1 | 1 | 535 |
| 12 | n=12 cap=14 | 695 | 1.160 | 0 | 0 | True | 1 | 1 | 641 |
| 13 | n=13 cap=15 | 798 | 1.148 | 0 | 0 | True | 1 | 1 | 757 |
| 14 | n=14 cap=16 | 908 | 1.138 | 0 | 0 | True | 1 | 1 | 885 |
| 15 | n=15 cap=17 | 1025 | 1.129 | 0 | 0 | True | 1 | 1 | 1023 |
| 16 | n=16 cap=18 | 1149 | 1.121 | 0 | 0 | True | 1 | 1 | 1172 |
| 17 | n=17 cap=19 | 1280 | 1.114 | 0 | 0 | True | 1 | 1 | 1330 |
| 18 | n=18 cap=20 | 1418 | 1.108 | 0 | 0 | True | 1 | 1 | 1498 |
| 19 | n=19 cap=21 | 1563 | 1.102 | 0 | 0 | True | 1 | 1 | 1676 |
| 20 | n=20 cap=22 | 1715 | 1.097 | 0 | 0 | True | 1 | 1 | 1864 |

20/20 points match the predicted stack_peak.

## lcs

Predicted law: stack_peak = 0 (bottom-up DP; m = n)

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 1 | m=n=1 | 14 |  | 0 | 0 | True | 1 | 1 | 7 |
| 2 | m=n=2 | 29 | 2.071 | 0 | 0 | True | 1 | 1 | 17 |
| 3 | m=n=3 | 54 | 1.862 | 0 | 0 | True | 1 | 1 | 25 |
| 4 | m=n=4 | 85 | 1.574 | 0 | 0 | True | 1 | 1 | 40 |
| 5 | m=n=5 | 124 | 1.459 | 0 | 0 | True | 1 | 1 | 61 |
| 6 | m=n=6 | 169 | 1.363 | 0 | 0 | True | 1 | 1 | 86 |
| 7 | m=n=7 | 224 | 1.325 | 0 | 0 | True | 1 | 1 | 113 |
| 8 | m=n=8 | 285 | 1.272 | 0 | 0 | True | 1 | 1 | 149 |
| 9 | m=n=9 | 354 | 1.242 | 0 | 0 | True | 1 | 1 | 193 |
| 10 | m=n=10 | 429 | 1.212 | 0 | 0 | True | 1 | 1 | 245 |
| 11 | m=n=11 | 514 | 1.198 | 0 | 0 | True | 1 | 1 | 303 |
| 12 | m=n=12 | 605 | 1.177 | 0 | 0 | True | 1 | 1 | 367 |
| 13 | m=n=13 | 704 | 1.164 | 0 | 0 | True | 1 | 1 | 439 |
| 14 | m=n=14 | 809 | 1.149 | 0 | 0 | True | 1 | 1 | 517 |
| 15 | m=n=15 | 924 | 1.142 | 0 | 0 | True | 1 | 1 | 599 |
| 16 | m=n=16 | 1045 | 1.131 | 0 | 0 | True | 1 | 1 | 692 |
| 17 | m=n=17 | 1174 | 1.123 | 0 | 0 | True | 1 | 1 | 795 |
| 18 | m=n=18 | 1309 | 1.115 | 0 | 0 | True | 1 | 1 | 908 |
| 19 | m=n=19 | 1454 | 1.111 | 0 | 0 | True | 1 | 1 | 1029 |
| 20 | m=n=20 | 1605 | 1.104 | 0 | 0 | True | 1 | 1 | 1160 |

20/20 points match the predicted stack_peak.

## edit_distance

Predicted law: stack_peak = 0 (bottom-up DP; m = n)

| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 1 | m=n=1 | 26 |  | 0 | 0 | True | 1 | 1 | 10 |
| 2 | m=n=2 | 46 | 1.769 | 0 | 0 | True | 1 | 1 | 25 |
| 3 | m=n=3 | 83 | 1.804 | 0 | 0 | True | 1 | 1 | 42 |
| 4 | m=n=4 | 125 | 1.506 | 0 | 0 | True | 1 | 1 | 67 |
| 5 | m=n=5 | 179 | 1.432 | 0 | 0 | True | 1 | 1 | 99 |
| 6 | m=n=6 | 238 | 1.330 | 0 | 0 | True | 1 | 1 | 141 |
| 7 | m=n=7 | 314 | 1.319 | 0 | 0 | True | 1 | 1 | 189 |
| 8 | m=n=8 | 395 | 1.258 | 0 | 0 | True | 1 | 1 | 247 |
| 9 | m=n=9 | 488 | 1.235 | 0 | 0 | True | 1 | 1 | 313 |
| 10 | m=n=10 | 586 | 1.201 | 0 | 0 | True | 1 | 1 | 387 |
| 11 | m=n=11 | 701 | 1.196 | 0 | 0 | True | 1 | 1 | 467 |
| 12 | m=n=12 | 821 | 1.171 | 0 | 0 | True | 1 | 1 | 559 |
| 13 | m=n=13 | 953 | 1.161 | 0 | 0 | True | 1 | 1 | 666 |
| 14 | m=n=14 | 1090 | 1.144 | 0 | 0 | True | 1 | 1 | 785 |
| 15 | m=n=15 | 1244 | 1.141 | 0 | 0 | True | 1 | 1 | 912 |
| 16 | m=n=16 | 1403 | 1.128 | 0 | 0 | True | 1 | 1 | 1051 |
| 17 | m=n=17 | 1574 | 1.122 | 0 | 0 | True | 1 | 1 | 1200 |
| 18 | m=n=18 | 1750 | 1.112 | 0 | 0 | True | 1 | 1 | 1359 |
| 19 | m=n=19 | 1943 | 1.110 | 0 | 0 | True | 1 | 1 | 1526 |
| 20 | m=n=20 | 2141 | 1.102 | 0 | 0 | True | 1 | 1 | 1703 |

20/20 points match the predicted stack_peak.
