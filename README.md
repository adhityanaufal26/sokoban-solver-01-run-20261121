# sokoban-solver-01-run-20261121

[![bounty](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/adhityanaufal26/sokoban-solver-01-run-20261121/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121/leaderboard)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/adhityanaufal26/sokoban-solver-01-run-20261121/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121/leaderboard)

A push-optimal Sokoban solver for make.fun's generated levels (a hallway with 1–4 rooms of 3–4 boxes each). It decomposes each level into its hallway and rooms, solves every room with push-based A* (player-region normalization, min-cost box→goal matching over pull-BFS push distances, dead-square and freeze-deadlock pruning, transposition table), concatenates the room solutions with hallway walks, and replay-verifies the full move string before writing it. A whole-board solver with the same machinery is the fallback when a level does not decompose. Search budgets are deterministic expansion counts (no clock, no randomness), so two runs write identical bytes. On the practice set it solves all 5 instances at the push-optimal count.

## Run it

`node main.ts` reads `/input/<id>/level.txt` and writes `/output/<id>/solution.txt` (set `MAKEFUN_INPUT_DIR` / `MAKEFUN_OUTPUT_DIR` locally to choose other directories). Node 22+, no dependencies.

Built for [make.fun](https://make.fun/).
