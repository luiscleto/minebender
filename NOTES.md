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

- The UI must render exactly `G.knowledge(g)`, `G.status(g)` and `G.flagged(g, ·)` (later: a `display(g)` with its own laws); the laws are about
  those accessors.
- Generation laws cover shape, count and first-click safety, not the distribution.
- Which safe cell the assist reveals, and which provably safe cell an AssistTooEarly loss shows, are left free (the user does not mind, provided it is safe).

## Spec gaps found (Q2: a law passed while behaviour was wrong)

- (found in review, not yet in behaviour) "Games terminate" rests on monotone + bridge: an action that
  changes the knowledge must reveal a cell. On a board with zero rows, bridge cannot pin the
  knowledge's width (no row to measure), so the width field could change forever without a reveal.
  Harmless in practice: every level has at least 9 rows.

## Where proofs got hard (Q3)

(none yet)

## Bend lessons

- `for x: A where P` turns `x` into a pair everywhere in the law; use a separate `for h: P` hypothesis.
- `match` only inspects parameters or pattern-bound variables; a computed value needs a helper def.
- Imported constructors are qualified like defs: `T.Pos{..}`, `case T.Pos{x, y}`.
- Termination reads arguments left to right; put the shrinking one first (`play(acts, g)`).
- A file importing a LAWS.bend with open laws will not run `main`. `examples.bend` checks the spec on
  concrete boards as `{==}` defs instead (`bend examples.bend --check-only`); a wrong value fails
  with expected/observed.
- A `+v` stays usable after `match v`: no need to rebuild a copyable value from its fields.
- A refutation of `{1n+n == 0n}`: rewrite through `disc` (0n to Empty, 1n+p to Unit), answer `Unit{}`.
