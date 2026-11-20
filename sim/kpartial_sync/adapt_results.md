# Adaptive control, n = 100, seeds [1, 2, 3]

Latencies in ms, pooled over seeds. *extra*: symbol and pull KB per validator per round, and as a share of push. *misses*: partial blocks not repaired by symbols before the repair deadline (fixed: pull_timer, 500 ms; adaptive: twice the round time), per validator per round. *loss est.*, *margin*: means over validators at the end of the run. *catch-up*: outage only.

| scenario | budget | decide p50 / p99 / max | round | extra KB (%) | misses | loss est. | margin | catch-up |
|---|---|---|---|---|---|---|---|---|
| p = 0.1% | fixed, true loss (oracle) | 247 / 291 / 381 | 86 | 12.2 (1.1%) | 0.000 | — | — |  |
| p = 0.1% | fixed, assumes 1% | 242 / 283 / 311 | 85 | 37.2 (3.3%) | 0.000 | — | — |  |
| p = 0.1% | adaptive | 247 / 292 / 446 | 86 | 14.5 (1.3%) | 0.001 | 0.0019 | 1.3 |  |
| p = 1.0% | fixed, true loss (oracle) | 258 / 336 / 359 | 92 | 38.2 (3.4%) | 0.000 | — | — |  |
| p = 1.0% | fixed, assumes 1% | 258 / 336 / 359 | 92 | 38.2 (3.4%) | 0.000 | — | — |  |
| p = 1.0% | adaptive | 258 / 292 / 310 | 89 | 41.4 (3.7%) | 0.000 | 0.0105 | 1.3 |  |
| p = 5.0% | fixed, true loss (oracle) | 322 / 361 / 397 | 109 | 132.7 (12.0%) | 0.000 | — | — |  |
| p = 5.0% | fixed, assumes 1% | 1274 / 1745 / 1839 | 426 | 153.9 (13.9%) | 21.606 | — | — |  |
| p = 5.0% | adaptive | 314 / 349 / 369 | 107 | 154.3 (14.0%) | 0.000 | 0.0511 | 5.4 |  |
| 5% of links at 20%, p = 0.1% | fixed, true loss (oracle) | 262 / 315 / 403 | 91 | 40.0 (3.6%) | 0.000 | — | — |  |
| 5% of links at 20%, p = 0.1% | fixed, assumes 1% | 265 / 362 / 478 | 98 | 38.7 (3.5%) | 0.000 | — | — |  |
| 5% of links at 20%, p = 0.1% | adaptive | 253 / 328 / 359 | 89 | 48.4 (4.4%) | 0.001 | 0.0142 | 1.4 |  |
| 5% of links at 20%, p = 0.1% | adaptive, reports only | 258 / 302 / 330 | 90 | 41.5 (3.8%) | 0.002 | 0.0154 | 1.7 |  |
| jitter 30 ms, p = 0.1% | fixed, true loss (oracle) | 501 / 758 / 946 | 178 | 12.7 (1.1%) | 0.005 | — | — |  |
| jitter 30 ms, p = 0.1% | fixed, assumes 1% | 480 / 539 / 607 | 166 | 36.8 (3.3%) | 0.000 | — | — |  |
| jitter 30 ms, p = 0.1% | adaptive | 491 / 577 / 625 | 172 | 18.7 (1.7%) | 0.005 | 0.0032 | 3.5 |  |
| jitter 30 ms, p = 0.1% | adaptive, reports only | 493 / 675 / 704 | 175 | 18.0 (1.6%) | 0.007 | 0.0030 | 3.9 |  |
| outage 500 ms, p = 0.1% | fixed, true loss (oracle) | 248 / 302 / 895 | 86 | 13.4 (1.2%) | 0.000 | — | — | 341 |
| outage 500 ms, p = 0.1% | fixed, assumes 1% | 244 / 287 / 806 | 85 | 38.8 (3.5%) | 0.000 | — | — | 298 |
| outage 500 ms, p = 0.1% | adaptive | 247 / 299 / 924 | 86 | 15.4 (1.4%) | 0.004 | 0.0018 | 1.2 | 364 |
| outage 500 ms, p = 0.1% | adaptive, reports only | 247 / 342 / 908 | 87 | 14.7 (1.3%) | 0.005 | 0.0018 | 1.3 | 359 |
| p 0.1% → 5% (1.5–3 s) → 0.1% | fixed, assumes 0.1% | 250 / 1418 / 1899 | 124 | 21.5 (2.0%) | 2.624 | — | — |  |
| p 0.1% → 5% (1.5–3 s) → 0.1% | fixed, assumes 1% | 249 / 1038 / 1178 | 113 | 46.1 (4.2%) | 0.172 | — | — |  |
| p 0.1% → 5% (1.5–3 s) → 0.1% | fixed, assumes 5% | 252 / 358 / 387 | 92 | 122.0 (11.0%) | 0.000 | — | — |  |
| p 0.1% → 5% (1.5–3 s) → 0.1% | adaptive | 255 / 400 / 438 | 93 | 66.4 (6.0%) | 0.099 | 0.0090 | 2.1 |  |
| p 0.1% → 5% (1.5–3 s) → 0.1% | adaptive, reports only | 252 / 623 / 687 | 100 | 60.3 (5.4%) | 0.937 | 0.0061 | 5.7 |  |
