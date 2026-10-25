# minebender — project brief

Handed over from an earlier Claude session (2026-10-25). Read this whole file first.

## Why this exists

A trial of Bend 2's "law-driven development": the human states precise laws, the agent writes the code
and proves the laws, and the proof checker (not human code review) is the gate. The point is to learn
whether that workflow holds up on something non-trivial, so the process matters as much as the game.

Questions to answer by the end (keep notes in `NOTES.md` as you go):
1. How much did the user have to read beyond `LAWS.bend` to trust the result?
2. Did any law pass while behaviour was wrong? Each such case is a gap in the spec — record it.
3. Where did proofs get hard or impossible, and what was done about it?

## Bend facts (verified on this machine)

- Bend 2.0.39, installed in `~/.bend`, on PATH as `bend` (`~/.local/bin/bend`).
- **Read `bend guide` before writing any Bend.** `bend base` prints the standard library.
- Convention (from the guide): `LAWS.bend` at the root imports the code and states laws as open
  claims; `PROOF.bend` imports `LAWS.bend` and proves each law with a def of the same name.
  `bend PROOF.bend` prints `ALL PROOFS CHECK` only when every law holds; `--verdict` re-checks with a
  small kernel that is itself proven in Lean, and rejects `@unsafe` or foreign code.
- No tactics: propositions are types, proofs are defs. Recursion must be structurally decreasing
  unless marked `@unsafe` (which falls outside the proof guarantees).
- IO: files, sockets, `IO.random_u32`, `IO.now`; foreign C and JS imports exist.
  `bend page.html -o dir` bundles a web page that imports `.bend` files (not tested yet).
- Bend checks for updates daily (`BEND_NO_TELEMETRY=1` disables it).
- Large real-world reference: github.com/i2cjak/Backplane, whose `LAWS.bend`/`PROOF.bend` show the
  conventions at scale (installed locally as the Backplane app; its source is not cloned here).

## Ownership rule

`LAWS.bend` belongs to the user. Draft laws in plain English *and* Bend for them to review; once they
approve a law, never weaken or delete it without their explicit consent. Code and `PROOF.bend` are yours.

## The game

Minesweeper with a **no-guess assist button**: when the player has no option other than a random guess,
they can press the button and a safe tile is revealed. If they press it while a guess-free option
exists, they lose, and the game shows them a cell they could have revealed safely.

### Design decisions — PROPOSED, confirm with the user before writing laws

1. **Flags are not knowledge.** They are the player's beliefs; a wrong flag must not make the game
   claim a deduction exists.
2. **The total mine count is knowledge.** The player sees it, so endgame counting arguments count.
3. **An "option" means a hidden cell that is safe in every mine layout consistent with what is
   visible.** A provably-mined cell is not a move (any safe cell it implies is already covered).

### Core definitions (the user owns these)

- `consistent(view, layout)`: layout has exactly N mines, none on a revealed cell, and every revealed
  number equals its count of adjacent mines in the layout.
- `provably_safe(view, c)`: `c` is hidden and no consistent layout has a mine on `c`.
- `stuck(view)`: no cell is provably safe.

### Laws to draft

Button:
- **Bridge law:** the real board is always consistent with the view after every move. Without it the
  other laws say nothing about the actual game.
- Witness soundness: if the solver returns cell `c`, then `provably_safe(view, c)`.
- Stuck soundness: if the solver says stuck, then `stuck(view)` (the hard direction — a claim over
  every layout).
- Pressing when stuck reveals a cell with no mine on the real board (one exists unless already won).
- Pressing when not stuck loses and shows a provably safe cell.
- After the game ends, no action changes the state.

Game:
- Numbers equal adjacent mine counts.
- Revealing a mine loses.
- Revealing a 0 reveals exactly its connected 0-region plus the numbered border cells around it.
- Won iff every non-mine cell is revealed.
- Each reveal strictly increases the revealed count, so games terminate.
- Generated boards have exactly N mines; first click is safe (if the user wants that rule).

### Proof strategy

State `provably_safe` in `LAWS.bend` as a brute-force spec over all layouts (obviously correct,
exponential). The fast solver (frontier cells adjacent to revealed numbers, split into independent
components, backtracking, plus the global mine-count argument for non-frontier cells) is then proven
equal to the spec. That equivalence proof is the real test. Deciding consistency is NP-complete in
general (Kaye 2000), so the fast solver is "fast on real boards", not polynomial.

### Scope

- Pure core first (state, actions, solver) with no UI. Random generation is IO; only "exactly N mines"
  and "first click safe" get laws.
- UI afterwards: terminal or the Bend web-page bundle; UI stays outside the proofs.
- Stretch: on a penalty, also show which numbers force the shown cell safe (minimal explanation search).

## Suggested first steps

1. Read `bend guide`; skim Backplane's `LAWS.bend` header for conventions.
2. Confirm the three design decisions with the user.
3. `git init`, add a check script that runs `bend PROOF.bend` (and `--verdict`).
4. Draft the core definitions + the first handful of laws for user review, then implement and prove.

## User working preferences

- Prefers maintained upstream tools over custom code; justify anything bespoke.
- No `curl | bash` without inspecting the content first. Commands needing sudo: hand them over one at a
  time, explained, as a single line.
