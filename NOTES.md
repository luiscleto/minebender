# minebender: notes

Running notes for the law-driven-development trial (see BRIEF.md for the questions to answer).

## Decisions (confirmed by the user, 2026-10-25)

1. Flags are not knowledge. `consistent` and the knowledge ignore them. Flags do matter for actions:
   double-clicking (chording) a number reveals its hidden, unflagged neighbours.
2. The total mine count is knowledge: a consistent layout has exactly N mines.
3. An option is a hidden cell that is safe in every consistent layout. Provably mined cells are not
   moves.
4. The first click is always safe: mines are placed after it, avoiding that cell.
   Later (user's choice, after checking what later Windows versions did): when there is room
   (n + 9 <= w*h, true for every level and Custom cap) its neighbours are kept free too, so the
   first click always opens an area, as in Windows Vista and later. XP only guaranteed the cell
   itself (checked in the XPWinmine source: a first-click mine moves to the first free cell from
   the top-left).
5. Levels follow Windows XP (checked against a source restoration, github.com/12UE/XPWinmine):
   Beginner 9x9/10, Intermediate 16x16/40, Expert 30x16/99; Custom clamps width 9..30, height 9..25,
   mines 10..999, then caps mines at w*h - 10.
6. Chording only when flagged neighbours equal the number; clicking a flagged cell does nothing
   (both approved).
7. UI: leaning to a web page (`bend page.html -o dist` gives static HTML + plain JS with no Bend
   runtime needed, so it can be hosted on GitHub Pages; tested on a toy page).

## Approved laws

Reviewed one at a time by the user; never weaken or delete these without their consent.

- 2026-10-25: level_beginner, level_intermediate, level_expert, level_custom, frozen, reveal_flagged, reveal_unflagged, flag_no_knowledge, flag_toggle, flag_others, flag_revealed
- 2026-10-25 definitions: at, mine, on_board, rows_wide, shaped, same, dist, within_one, adjacent, row_cells, cells.go, cells, touching, neighbours, count_mines, adj_mines, row_mines, total_mines, seen, is_hidden, hidden, revealed, agrees, agrees_all, consistent, ProvablySafe, Stuck, play, Reachable
- 2026-10-25: bridge, won_iff (+ defs is_won, all_safe_revealed.go, all_safe_revealed), monotone
- 2026-10-25 definitions: zero, zero_walk
- 2026-10-25: open_mine (now also shows Boom), open_safe (on-board premise dropped) (+ def is_lost), flood_complete (safe premise dropped), flood_exact, flags_hidden (user-proposed)
- 2026-10-25 definitions: flags_among, hidden_unflagged, chord_targets.pick, chord_targets.go, chord_targets
  (all_safe_revealed simplified afterwards, same meaning: passes +v on instead of rebuilding it)
- 2026-10-25: chord (+ def reveals), assist_stuck, assist_too_early, gen_shape, gen_count, gen_first_safe
- 2026-10-25 (later, user chose "option 1"): the assist action carries a random number, `Assist{k}`;
  `assist_stuck` and `assist_too_early` gained `for k: Nat` and use `T.Assist{k}`. Same guarantees,
  for every k. The number picks which safe cell opens when stuck (frontier first, from a random
  point), which the user asked for; that preference itself is not a law.
- 2026-10-25 (after the UI went live): the display section: Tile type, tile, tile_of, is_covered,
  display_play, display_blast, display_hint, display_mines (approved as drafted; display_mines kept
  loose on purpose: every mine is visible after the game, not which XP tile it gets).
- 2026-10-25: gen_opening (first click opens an area when there is room); the generator now keeps a
  zone free (the first cell, or it and its neighbours), and its proofs gained a bound: at most 9
  board cells are within one step of a cell.

## Choices settled during review

- The flood, the chord's own reveals and the assist open cells through `G.open`, which ignores
  flags; `flags_hidden` then makes the game clear any flag on a cell it reveals.
- Witness and stuck soundness of the solver are not laws: `assist_stuck` and `assist_too_early`
  state the button's behaviour directly against the brute-force spec, so the solver's own laws
  become lemmas in PROOF.bend (user had no preference; kept as proposed).
- Laws about play quantify over reachable games (any actions from a fresh game on a well-shaped
  layout). `frozen`, the flag laws (except `flags_hidden`), `reveal_*` and `chord` hold for every
  game state.
- No law about the randomness of generated boards (user agreed to skip it).
- `level_custom` covers the defs `clamp` and `custom`.

## Trust boundary (what the laws do not cover)

- The screen is `G.display(g)`, a grid of tiles; the display laws (end of LAWS.bend) tie it to the
  knowledge, flags and status. Not pinned by them: which tile a mine gets after the game (XP style
  in the code), and the crossed-out wrong flags after a loss. What is *not* proven is the JavaScript between
  that grid and the pixels: `docs/index.html` (draws the tile codes it is sent; turns clicks, taps and
  long-presses into Reveal/Chord/Flag/Assist) and `docs/worker.js` (holds the game, converts lists,
  feeds `crypto.getRandomValues` into `place_mines`). Neither decides anything about the rules; read
  them to check that. `ui.bend` is the whole interface they call. Also outside the laws: the timer,
  the mine counter (mines minus `UI.flags`, shown as 0 once won), the messages, and the statistics
  (localStorage, per board spec: five best times with dates, played/won/win %, current and longest
  streaks, Windows 7 style; a game abandoned after its first click counts as a loss, including a
  page closed mid-game, via a "pending" marker read on the next load).
- How the board is drawn on screen: on a portrait screen a board wider than tall is drawn turned a
  quarter turn (the player can rotate any non-square board, and zoom the cells from 16 to 48 px).
  Only the drawing and the mapping from a tapped cell back to the game's (x, y) change.
- Before the first click no game exists (mines are placed on the first reveal), so flags, chords and
  the assist do nothing until then; the board shown is `UI.idle`, Bend's display of an empty board.
- Generation laws cover shape, count and first-click safety, not the distribution.
- Which safe cell the assist reveals, and which provably safe cell an AssistTooEarly loss shows, are left free (the user does not mind, provided it is safe).

## Spec gaps found (Q2: a law passed while behaviour was wrong)

No case of a law passing while observed behaviour was wrong. Found during review:

- (found in review, not yet in behaviour) "Games terminate" rests on monotone + bridge: an action that
  changes the knowledge must reveal a cell. On a board with zero rows, bridge cannot pin the
  knowledge's width (no row to measure), so the width field could change forever without a reveal.
  Harmless in practice: every level has at least 9 rows.

## Status (2026-10-25)

All 30 approved laws (26 game laws and 4 display laws) are proven: `./check.sh` prints ALL PROOFS CHECK for `bend PROOF.bend` and for
`--verdict` (the Lean-proven BendTT kernel; needs Lean v4.34.0, installed with elan v4.2.4 into
`~/.elan`, checksum verified against the GitHub release). Self-play (`selfplay.bend`) wins every test
game.

Assist speed, Expert self-play through the page's module in node (25 games, 5,451 calls): mean
20 ms, worst 267 ms. Before the solver rework: mean 185 ms, worst 12.8 s, ~1 s whenever stuck.

Web page: https://cleto.dev/minebender/ (`docs/`, served by GitHub Pages; `./build.sh`
regenerates `docs/ui.mjs` from `ui.bend` with `bend ui.bend -o docs/ui.mjs`). The upstream page
bundler (`bend page.html -o dist`) was tried first, but it does not follow `new Worker(...)`, and the
game runs in a worker so a slow assist can never freeze the page (that was seconds before the solver
rework, now well under a second). So the page is three static files and no bundler.

Size: LAWS.bend ~660 lines (all approved) (user-owned); code ~1330 lines (types,
board, game, solver); laws and proofs together ~12,900 lines across LAWS.bend, PROOF.bend and 16
`proof_*.bend` lemma modules.

## Q1: what the user read beyond LAWS.bend

types.bend (the interface types), and nothing else: every definition and law in LAWS.bend was
reviewed one by one (with plain-English and Bend for each). The code and proofs were not read; the
gate is the checker. The user did need a Bend primer along the way (quantities `&1`/`&2`/`+`,
templates, why loops become recursion over lists), and spotted several simplifications in the spec
itself (`!=` instead of a helper, `not same` in `adjacent`, the `flags_hidden` law).

Later rounds kept the same pattern. The display laws were drafted and proven while the user was
away, then reviewed one by one after the fact and approved unchanged; the Tile type was shown in
that review. For the solver rework and the assist's random pick, the user read neither code nor
proofs: they asked for the standard published method, approved the one law-text change (`Assist{k}`)
in prose, and judged the result by the live page and the reported timings. Beyond LAWS.bend, their
main check was playing the game (which is how the slow assist and the top-left pick were found:
behaviour the laws allowed but the user did not want, rather than behaviour a law got wrong).

## Where proofs got hard (Q3)

- Rewrite direction (`%e`) was the most frequent friction: dozens of fixes. A fixed rule
  (`e : {new == old}`) helped; error messages show expected/observed terms, which made it fast.
- Function-typed hypotheses are affine (usable once, even erased), so "for every cell" invariants
  could not be passed around as functions. Every invariant became a Bool check over all cells plus
  a "read it back at one cell" lemma (equalities are copyable).
- No mutual recursion, and a proof helper cannot call the lemma it serves: induction hypotheses are
  passed into helpers as closures (`e2 => lemma(rest, ...)`).
- A law's `for x` without `+` cannot be reused in its proof, and a proof def cannot add `+`. The
  user's laws were left untouched: each `L.law` forwards to a restated lemma with `for +x`.
  (Correction to what I told the user during review: `for` lines *do* need `+` when a proof reuses
  the variable; the restated lemmas carry it.)
- `flood_exact` needs an actual path for every cell the flood reveals. The flood code was changed to
  carry a ghost path with each queued cell (used only by the proofs).
- The solver's completeness (no layout found ⇒ none exists) was the largest proof: pruning
  soundness needed grid sums = cell sums (generic templated lemma), inequality arithmetic, and
  completion/coverage invariants for the partial layout. The code was changed in one place for it:
  the to-do ordering used a pair (hard to take apart in proofs) and became two filters.
- The solver is proven against the brute-force definition of `ProvablySafe`. Its first version
  searched in reading order: easy to prove, but 1 s to 12.8 s on Expert. The rework follows the
  standard constraint approach to Minesweeper (connected components of the frontier, searched
  separately: Becerra, "Algorithmic Approaches to Playing Minesweeper", Harvard 2015, ch. 6;
  Tatham's Mines solver was read too, but it is heuristic and the assist law needs an exact
  answer). Two tricks kept the proof small:
  - The component order is a heuristic prefix put in front of the old, proven order. The search
    skips cells already assigned, so the proofs only need "every cell is still in the list" and
    "every entry is one of the solve's own": no proof that the components are right.
  - The search carries running counts instead of rescanning the grid; rather than re-prove the
    search, `proof_speed.bend` proves the counting search returns exactly what the old one returns
    (`dfs2_eq`), and the old lemmas do the rest.
  First prototypes were benchmarked unproven; one bad ordering ran for 10+ minutes and maxed the
  user's fan. Benchmarks now run under `nice` with a time limit.

## Bend lessons

- `for x: A where P` turns `x` into a pair everywhere in the law; use a separate `for h: P` hypothesis.
- `match` only inspects parameters or pattern-bound variables; a computed value needs a helper def.
- Imported constructors are qualified like defs: `T.Pos{..}`, `case T.Pos{x, y}`.
- Termination reads arguments left to right; put the shrinking one first (`play(acts, g)`).
- A file importing a LAWS.bend with open laws will not run `main`. `examples.bend` checks the spec on
  concrete boards as `{==}` defs instead (`bend examples.bend --check-only`); a wrong value fails
  with expected/observed.
- A `+v` stays usable after `match v`: no need to rebuild a copyable value from its fields.
- `%e : P` with `e : {a == b}`: the goal must be P with b at `_`; it becomes P with a. Rule of thumb:
  `e : {new == old}`. Same for an inline `{%e : P; x : T}`: T is old (P with b), x has P with a.
  (use `Equal.sym` to go the other way).
- A refutation of `{1n+n == 0n}`: rewrite through `disc` (0n to Empty, 1n+p to Unit), answer `Unit{}`.
