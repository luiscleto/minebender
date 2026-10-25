# minebender: notes

Running notes for the law-driven-development trial (see BRIEF.md for the questions to answer).

## Decisions (confirmed by the user, 2026-10-25)

1. Flags are not knowledge. `consistent` and the knowledge ignore them. Flags do matter for actions:
   double-clicking (chording) a number reveals its hidden, unflagged neighbours.
2. The total mine count is knowledge: a consistent layout has exactly N mines.
3. An option is a hidden cell that is safe in every consistent layout. Provably mined cells are not
   moves.
4. The first click is always safe: mines are placed after it, avoiding that cell.
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

- The screen is `G.display(g)`, a grid of tiles; the DRAFT display laws (end of LAWS.bend, awaiting
  review) tie it to the knowledge, flags and status. What is *not* proven is the JavaScript between
  that grid and the pixels: `docs/index.html` (draws the tile codes it is sent; turns clicks, taps and
  long-presses into Reveal/Chord/Flag/Assist) and `docs/worker.js` (holds the game, converts lists,
  feeds `crypto.getRandomValues` into `place_mines`). Neither decides anything about the rules; read
  them to check that. `ui.bend` is the whole interface they call. Also outside the laws: the timer,
  the mine counter (mines minus `UI.flags`, shown as 0 once won) and the messages.
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

All 25 approved laws, plus the 4 DRAFT display laws, are proven: `./check.sh` prints ALL PROOFS CHECK for `bend PROOF.bend` and for
`--verdict` (the Lean-proven BendTT kernel; needs Lean v4.34.0, installed with elan v4.2.4 into
`~/.elan`, checksum verified against the GitHub release). Self-play (`selfplay.bend`) wins every test
game; on Expert a solver call takes ~150 ms, ~1 s when genuinely stuck.

Web page: https://luiscleto.github.io/minebender/ (`docs/`, served by GitHub Pages; `./build.sh`
regenerates `docs/ui.mjs` from `ui.bend` with `bend ui.bend -o docs/ui.mjs`). The upstream page
bundler (`bend page.html -o dist`) was tried first, but it does not follow `new Worker(...)`, and the
game must run in a worker: the assist takes ~1 s in the browser when stuck (7.8 s worst seen on
Expert), which would freeze the page. So the page is three static files and no bundler.

Size: LAWS.bend 655 lines (573 approved + the display draft) (user-owned); code ~1030 lines (types, board, game, solver); proofs
~9400 lines in PROOF.bend + 13 `proof_*.bend` lemma modules (solver correctness alone ~2600).

## Q1: what the user read beyond LAWS.bend

types.bend (the interface types), and nothing else: every definition and law in LAWS.bend was
reviewed one by one (with plain-English and Bend for each). The code and proofs were not read; the
gate is the checker. The user did need a Bend primer along the way (quantities `&1`/`&2`/`+`,
templates, why loops become recursion over lists), and spotted several simplifications in the spec
itself (`!=` instead of a helper, `not same` in `adjacent`, the `flags_hidden` law).

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
- The fast solver is proven against the brute-force definition of `ProvablySafe`; the search is
  "frontier first" depth-first with bound pruning, not component-split (the brief's suggestion), to
  keep the proof one induction.

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
