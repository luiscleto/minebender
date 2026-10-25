import Base
import ./types.bend as T
import ./game.bend as G

# minebender: the laws.
#
# APPROVED by the owner on 2026-10-25, law by law (see NOTES.md). Never weaken
# or delete a law or definition here without the owner's explicit consent.
#
# The game is reached only through: G.fresh, G.step, G.open, G.knowledge,
# G.status, G.flagged, G.setup and G.place_mines. Everything else below is a
# definition owned by these laws, written to be obviously right rather than
# fast; the game's own code is free to compute the same things differently.

# ==========================================================================
# Definitions: the board
# ==========================================================================

# The value of grid g at p, or d when p is off the grid.
def at(-A: Data, d: A, g: T.Grid(A), p: T.Pos) -> A:
  match p:
    case T.Pos{x, y}:
      row = Maybe.default(&2, List<&2, A>, List.get(&2, List<&2, A>, g, y), Nil{})
      Maybe.default(&2, A, List.get(&2, A, row, x), d)

def mine(layout: T.Grid(Bool), p: T.Pos) -> Bool:
  at(Bool, False{}, layout, p)

def on_board(w: Nat, h: Nat, p: T.Pos) -> Bool:
  match p:
    case T.Pos{x, y}:
      Nat.is_lt(x, w) && Nat.is_lt(y, h)

def same(p: T.Pos, q: T.Pos) -> Bool:
  match p q:
    case T.Pos{px, py} T.Pos{qx, qy}:
      Nat.is_eq(px, qx) && Nat.is_eq(py, qy)

def dist(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.sub(a, b), Nat.sub(b, a))

# p and q are at most one step apart in each direction (or the same cell).
def within_one(p: T.Pos, q: T.Pos) -> Bool:
  match p q:
    case T.Pos{px, py} T.Pos{qx, qy}:
      Nat.is_le(dist(px, qx), 1n) && Nat.is_le(dist(py, qy), 1n)

# p and q are two different cells that touch, by a side or a corner.
def adjacent(+p: T.Pos, +q: T.Pos) -> Bool:
  Bool.not(same(p, q)) && within_one(p, q)

# The cells of row y, from column 0 up.
def row_cells(+y: Nat, xs: List<&2, Nat>) -> List<&2, T.Pos>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      T.Pos{x, y} <> row_cells(y, t)

def cells.go(+w: Nat, ys: List<&2, Nat>) -> List<&2, T.Pos>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> t:
      List.append(&2, T.Pos, row_cells(y, List.range(w)), cells.go(w, t))

# Every cell of a w-by-h board, row by row.
def cells(w: Nat, h: Nat) -> List<&2, T.Pos>:
  cells.go(w, List.range(h))

# The cells of qs adjacent to p, in the order of qs.
def touching(+p: T.Pos, qs: List<&2, T.Pos>) -> List<&2, T.Pos>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> t:
      List.filter.put(T.Pos, q, touching(p, t), adjacent(p, q))

# The cells of the board adjacent to p, row by row.
def neighbours(w: Nat, h: Nat, p: T.Pos) -> List<&2, T.Pos>:
  touching(p, cells(w, h))

def count_mines(+layout: T.Grid(Bool), ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case q <> t:
      Nat.add(Bool.pick(Nat, mine(layout, q), 1n, 0n), count_mines(layout, t))

# The number a revealed safe cell p must show.
def adj_mines(w: Nat, h: Nat, layout: T.Grid(Bool), p: T.Pos) -> Nat:
  count_mines(layout, neighbours(w, h, p))

def row_mines(row: List<&2, Bool>) -> Nat:
  match row:
    case Nil{}:
      0n
    case b <> t:
      Nat.add(Bool.pick(Nat, b, 1n, 0n), row_mines(t))

def total_mines(layout: T.Grid(Bool)) -> Nat:
  match layout:
    case Nil{}:
      0n
    case r <> t:
      Nat.add(row_mines(r), total_mines(t))

def rows_wide(-A: Data, +w: Nat, g: T.Grid(A)) -> Bool:
  match g:
    case Nil{}:
      True{}
    case r <> t:
      Nat.is_eq(List.length(&2, A, r), w) && rows_wide(A, w, t)

# g has exactly h rows of exactly w cells.
def shaped(-A: Data, w: Nat, h: Nat, +g: T.Grid(A)) -> Bool:
  Nat.is_eq(List.length(&2, List<&2, A>, g), h) && rows_wide(A, w, g)

# ==========================================================================
# Definitions: knowledge
# ==========================================================================

def seen(v: T.Knowledge, p: T.Pos) -> T.Seen:
  match v:
    case T.Knowledge{w, h, n, rows}:
      at(T.Seen, T.Hidden{}, rows, p)

def is_hidden(s: T.Seen) -> Bool:
  match s:
    case T.Hidden{}:
      True{}
    case o:
      False{}

# p is a cell of the board that the player cannot see.
def hidden(v: T.Knowledge, +p: T.Pos) -> Bool:
  match v:
    case T.Knowledge{w, h, n, rows}:
      on_board(w, h, p) && is_hidden(at(T.Seen, T.Hidden{}, rows, p))

# p is a cell of the board that the player can see.
def revealed(v: T.Knowledge, +p: T.Pos) -> Bool:
  match v:
    case T.Knowledge{w, h, n, rows}:
      on_board(w, h, p) && Bool.not(is_hidden(at(T.Seen, T.Hidden{}, rows, p)))

# What the player sees at p agrees with the layout.
def agrees(w: Nat, h: Nat, +layout: T.Grid(Bool), +p: T.Pos, s: T.Seen) -> Bool:
  match s:
    case T.Hidden{}:
      True{}
    case T.Shown{k}:
      Bool.not(mine(layout, p)) && Nat.is_eq(adj_mines(w, h, layout, p), k)
    case T.Boom{}:
      mine(layout, p)

def agrees_all(+w: Nat, +h: Nat, +rows: T.Grid(T.Seen), +layout: T.Grid(Bool),
  ps: List<&2, T.Pos>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> t:
      agrees(w, h, layout, p, at(T.Seen, T.Hidden{}, rows, p))
        && agrees_all(w, h, rows, layout, t)

# The layout could be the real one, given everything the player sees: it has
# the board's shape, exactly the announced number of mines, a mine under
# every Boom, none under a number, and every number counts its neighbours.
def consistent(v: T.Knowledge, +layout: T.Grid(Bool)) -> Bool:
  match v:
    case T.Knowledge{+w, +h, n, +rows}:
      shaped(Bool, w, h, layout) && shaped(T.Seen, w, h, rows)
        && Nat.is_eq(total_mines(layout), n)
        && agrees_all(w, h, rows, layout, cells(w, h))

# p is hidden, and no layout consistent with what the player knows has a mine on p.
def ProvablySafe(v: T.Knowledge, p: T.Pos) -> Type:
  {hidden(v, p) == True{} : Bool} &
  (@layout: T.Grid(Bool) ->
    {consistent(v, layout) == True{} : Bool} ->
    {mine(layout, p) == False{} : Bool})

# No cell is provably safe: the player's only options are guesses.
def Stuck(v: T.Knowledge) -> Type:
  @p: T.Pos -> ProvablySafe(v, p) -> Empty

# Every safe cell of the board is revealed.
def all_safe_revealed.go(+v: T.Knowledge, +layout: T.Grid(Bool), ps: List<&2, T.Pos>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> t:
      (mine(layout, p) || revealed(v, p)) && all_safe_revealed.go(v, layout, t)

def all_safe_revealed(+v: T.Knowledge, layout: T.Grid(Bool)) -> Bool:
  match v:
    case T.Knowledge{w, h, n, rows}:
      all_safe_revealed.go(v, layout, cells(w, h))

# A zero: a safe cell of the board with no adjacent mine.
def zero(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +p: T.Pos) -> Bool:
  on_board(w, h, p) && Bool.not(mine(layout, p))
    && Nat.is_eq(adj_mines(w, h, layout, p), 0n)

# Starting at p, the path steps from cell to adjacent cell of the board,
# leaving only zeros, and ends at q. The empty path goes from p to p.
def zero_walk(path: List<&2, T.Pos>, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +p: T.Pos, q: T.Pos) -> Bool:
  match path:
    case Nil{}:
      same(p, q)
    case +r <> t:
      zero(w, h, layout, p) && adjacent(p, r) && on_board(w, h, r)
        && zero_walk(t, w, h, layout, r, q)

# ==========================================================================
# Definitions: the game
# ==========================================================================

def is_won(s: T.Status) -> Bool:
  match s:
    case T.Won{}:
      True{}
    case o:
      False{}

def is_lost(s: T.Status) -> Bool:
  match s:
    case T.Lost{why}:
      True{}
    case o:
      False{}

# Take the actions in order.
def play(acts: List<&2, T.Action>, g: G.Game) -> G.Game:
  match acts:
    case Nil{}:
      g
    case a <> t:
      play(t, G.step(g, a))

# The game g arises from a fresh game on this layout by some actions.
def Reachable(w: Nat, h: Nat, layout: T.Grid(Bool), g: G.Game) -> Type:
  Exists(List<&2, T.Action>,
    acts => {play(acts, G.fresh(w, h, layout)) == g : G.Game})

def reveals(ps: List<&2, T.Pos>) -> List<&2, T.Action>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      T.Reveal{p} <> reveals(t)

# How many cells of qs are flagged.
def flags_among(+g: G.Game, qs: List<&2, T.Pos>) -> Nat:
  match qs:
    case Nil{}:
      0n
    case q <> t:
      Nat.add(Bool.pick(Nat, G.flagged(g, q), 1n, 0n), flags_among(g, t))

def hidden_unflagged(+g: G.Game, +v: T.Knowledge, qs: List<&2, T.Pos>) -> List<&2, T.Pos>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> t:
      List.filter.put(T.Pos, q, hidden_unflagged(g, v, t),
        hidden(v, q) && Bool.not(G.flagged(g, q)))

def chord_targets.pick(+g: G.Game, v: T.Knowledge, +ns: List<&2, T.Pos>, s: T.Seen) ->
  List<&2, T.Pos>:
  match s:
    case T.Shown{k}:
      Bool.pick(List<&2, T.Pos>, Nat.is_eq(flags_among(g, ns), k),
        hidden_unflagged(g, v, ns), Nil{})
    case o:
      Nil{}

def chord_targets.go(g: G.Game, +v: T.Knowledge, +p: T.Pos) -> List<&2, T.Pos>:
  match v:
    case T.Knowledge{w, h, n, rows}:
      chord_targets.pick(g, v, neighbours(w, h, p), seen(v, p))

# Chording on p: if p shows a number k and exactly k of its neighbours are
# flagged, the hidden unflagged neighbours of p, row by row; otherwise none.
def chord_targets(+g: G.Game, p: T.Pos) -> List<&2, T.Pos>:
  chord_targets.go(g, G.knowledge(g), p)

# ==========================================================================
# Laws: the real board
# ==========================================================================

# LAW: "The real board is always consistent with what the player sees."
# Without it, the knowledge laws below would say nothing about the real game.
# It also covers "every number equals its count of adjacent mines".
law bridge:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  {consistent(G.knowledge(g), layout) == True{} : Bool}

# LAW: "The game is won exactly when every safe cell is revealed."
law won_iff:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  {is_won(G.status(g)) == all_safe_revealed(G.knowledge(g), layout) : Bool}

# LAW: "A revealed cell stays revealed, showing the same thing."
# With bridge, this makes every action that changes the knowledge reveal at least
# one more cell, so a game has at most w*h such actions.
law monotone:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for a: T.Action
  for q: T.Pos
  for vis: {revealed(G.knowledge(g), q) == True{} : Bool}
  {seen(G.knowledge(G.step(g, a)), q) == seen(G.knowledge(g), q) : T.Seen}

# LAW: "Once the game is won or lost, no action changes anything."
law frozen:
  for g: G.Game
  for over: {G.status(g) != T.Playing{} : T.Status}
  for a: T.Action
  {G.step(g, a) == g : G.Game}

# ==========================================================================
# Laws: revealing
# ==========================================================================

# LAW: "Revealing a mine loses, naming that mine, and shows it as Boom."
law open_mine:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for p: T.Pos
  for boom: {mine(layout, p) == True{} : Bool}
  {G.status(G.open(g, p)) == T.Lost{T.Exploded{p}} : T.Status} &
  {seen(G.knowledge(G.open(g, p)), p) == T.Boom{} : T.Seen}

# LAW: "Revealing a safe cell never loses."
law open_safe:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for p: T.Pos
  for safe: {mine(layout, p) == False{} : Bool}
  {is_lost(G.status(G.open(g, p))) == False{} : Bool}

# LAW: "Revealing a cell p reveals every cell reached from p by a path
# through zeros" (so a 0 opens its whole 0-region and the numbers around it;
# for a mine, that is p alone).
law flood_complete:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for p: T.Pos
  for on: {on_board(w, h, p) == True{} : Bool}
  for q: T.Pos
  for path: List<&2, T.Pos>
  for walk: {zero_walk(path, w, h, layout, p, q) == True{} : Bool}
  {revealed(G.knowledge(G.open(g, p)), q) == True{} : Bool}

# LAW: "Revealing p reveals nothing else": every newly revealed cell is
# reached from p by a path through zeros. (For a mine, that is p alone.)
law flood_exact:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for p: T.Pos
  for q: T.Pos
  for before: {hidden(G.knowledge(g), q) == True{} : Bool}
  for after: {revealed(G.knowledge(G.open(g, p)), q) == True{} : Bool}
  exs path: List<&2, T.Pos>
  {zero_walk(path, w, h, layout, p, q) == True{} : Bool}

# LAW: "Clicking a flagged cell does nothing."
law reveal_flagged:
  for g: G.Game
  for p: T.Pos
  for flag: {G.flagged(g, p) == True{} : Bool}
  {G.step(g, T.Reveal{p}) == g : G.Game}

# LAW: "Clicking an unflagged cell reveals it."
law reveal_unflagged:
  for g: G.Game
  for p: T.Pos
  for flag: {G.flagged(g, p) == False{} : Bool}
  {G.step(g, T.Reveal{p}) == G.open(g, p) : G.Game}

# LAW: "Double-clicking a number reveals its hidden unflagged neighbours,
# one by one, row by row" (when exactly that many neighbours are flagged).
law chord:
  for g: G.Game
  for p: T.Pos
  {G.step(g, T.Chord{p}) == play(reveals(chord_targets(g, p)), g) : G.Game}

# ==========================================================================
# Laws: flags
# ==========================================================================

# LAW: "Flags are not knowledge": flagging changes neither what the player
# sees nor the game's status.
law flag_no_knowledge:
  for g: G.Game
  for p: T.Pos
  {G.knowledge(G.step(g, T.Flag{p})) == G.knowledge(g) : T.Knowledge} &
  {G.status(G.step(g, T.Flag{p})) == G.status(g) : T.Status}

# LAW: "Flagging a hidden cell during play toggles its flag."
law flag_toggle:
  for g: G.Game
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for p: T.Pos
  for hid: {hidden(G.knowledge(g), p) == True{} : Bool}
  {G.flagged(G.step(g, T.Flag{p}), p) == Bool.not(G.flagged(g, p)) : Bool}

# LAW: "Flagging p leaves every other cell's flag alone."
law flag_others:
  for g: G.Game
  for p: T.Pos
  for q: T.Pos
  for diff: {p != q : T.Pos}
  {G.flagged(G.step(g, T.Flag{p}), q) == G.flagged(g, q) : Bool}

# LAW: "Only hidden cells carry flags": revealing a flagged cell clears its
# flag, and no cell off the board is ever flagged.
law flags_hidden:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for q: T.Pos
  for flag: {G.flagged(g, q) == True{} : Bool}
  {hidden(G.knowledge(g), q) == True{} : Bool}

# LAW: "Flagging a cell that is not hidden does nothing."
law flag_revealed:
  for g: G.Game
  for p: T.Pos
  for vis: {hidden(G.knowledge(g), p) == False{} : Bool}
  {G.step(g, T.Flag{p}) == g : G.Game}

# ==========================================================================
# Laws: the no-guess assist
# ==========================================================================

# LAW: "Pressing the assist when stuck reveals a safe cell."
law assist_stuck:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for stuck: Stuck(G.knowledge(g))
  for k: Nat
  exs p: T.Pos
  {mine(layout, p) == False{} : Bool} &
  {hidden(G.knowledge(g), p) == True{} : Bool} &
  {G.step(g, T.Assist{k}) == G.open(g, p) : G.Game}

# LAW: "Pressing the assist when some cell is provably safe loses, and shows
# a provably safe cell; the knowledge is unchanged."
law assist_too_early:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for q: T.Pos
  for option: ProvablySafe(G.knowledge(g), q)
  for k: Nat
  exs p: T.Pos
  ProvablySafe(G.knowledge(g), p) &
  {G.status(G.step(g, T.Assist{k})) == T.Lost{T.AssistTooEarly{p}} : T.Status} &
  {G.knowledge(G.step(g, T.Assist{k})) == G.knowledge(g) : T.Knowledge}

# ==========================================================================
# Laws: levels, as in Windows XP
# ==========================================================================

def clamp(lo: Nat, hi: Nat, x: Nat) -> Nat:
  Nat.max(lo, Nat.min(hi, x))

# Windows XP's Custom Field dialog: width is clamped to 9..30, height to
# 9..25 and mines to 10..999, then mines are capped at width*height - 10.
def custom(w: Nat, h: Nat, m: Nat) -> T.Setup:
  +cw = clamp(9n, 30n, w)
  +ch = clamp(9n, 25n, h)
  T.Setup{cw, ch, Nat.min(clamp(10n, 999n, m), Nat.sub(Nat.mul(cw, ch), 10n))}

# LAW: "Beginner is 9 by 9 with 10 mines."
law level_beginner:
  {G.setup(T.Beginner{}) == T.Setup{9n, 9n, 10n} : T.Setup}

# LAW: "Intermediate is 16 by 16 with 40 mines."
law level_intermediate:
  {G.setup(T.Intermediate{}) == T.Setup{16n, 16n, 40n} : T.Setup}

# LAW: "Expert is 30 wide by 16 high with 99 mines."
law level_expert:
  {G.setup(T.Expert{}) == T.Setup{30n, 16n, 99n} : T.Setup}

# LAW: "A custom level is limited exactly as Windows XP limits it."
law level_custom:
  for w: Nat
  for h: Nat
  for m: Nat
  {G.setup(T.Custom{w, h, m}) == custom(w, h, m) : T.Setup}

# ==========================================================================
# Laws: board generation
# ==========================================================================

# LAW: "Generated boards have the requested shape."
law gen_shape:
  for w: Nat
  for h: Nat
  for n: Nat
  for first: T.Pos
  for rs: List<&2, U32>
  {shaped(Bool, w, h, G.place_mines(w, h, n, first, rs)) == True{} : Bool}

# LAW: "Generated boards have exactly n mines" (when they fit beside the first
# click).
law gen_count:
  for w: Nat
  for h: Nat
  for n: Nat
  for first: T.Pos
  for rs: List<&2, U32>
  for on: {on_board(w, h, first) == True{} : Bool}
  for fits: {Nat.is_lt(n, Nat.mul(w, h)) == True{} : Bool}
  {total_mines(G.place_mines(w, h, n, first, rs)) == n : Nat}

# LAW: "The first click is safe."
law gen_first_safe:
  for w: Nat
  for h: Nat
  for n: Nat
  for first: T.Pos
  for rs: List<&2, U32>
  {mine(G.place_mines(w, h, n, first, rs), first) == False{} : Bool}

# ==========================================================================
# Laws: the display
# ==========================================================================
# DRAFT, written while the owner was away: awaiting review. Everything above
# this section is approved.

# What the screen shows at p.
def tile(g: G.Game, p: T.Pos) -> T.Tile:
  at(T.Tile, T.Covered{}, G.display(g), p)

# How a cell looks given what the player sees there and their flag.
def tile_of(s: T.Seen, flag: Bool) -> T.Tile:
  match s:
    case T.Hidden{}:
      Bool.pick(T.Tile, flag, T.Flagged{}, T.Covered{})
    case T.Shown{n}:
      T.Number{n}
    case T.Boom{}:
      T.Blast{}

def is_covered(t: T.Tile) -> Bool:
  match t:
    case T.Covered{}:
      True{}
    case o:
      False{}

# LAW: "During play, the screen shows exactly what the player knows, and
# their flags": nothing about the hidden mines leaks onto the screen.
law display_play:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for playing: {G.status(g) == T.Playing{} : T.Status}
  for p: T.Pos
  for on: {on_board(w, h, p) == True{} : Bool}
  {tile(g, p) == tile_of(seen(G.knowledge(g), p), G.flagged(g, p)) : T.Tile}

# LAW: "After an explosion, the screen shows the mine that exploded."
law display_blast:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for p: T.Pos
  for lost: {G.status(g) == T.Lost{T.Exploded{p}} : T.Status}
  for on: {on_board(w, h, p) == True{} : Bool}
  {tile(g, p) == T.Blast{} : T.Tile}

# LAW: "After the assist is pressed too early, the screen shows the safe cell
# the player could have revealed."
law display_hint:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for s: T.Pos
  for lost: {G.status(g) == T.Lost{T.AssistTooEarly{s}} : T.Status}
  for on: {on_board(w, h, s) == True{} : Bool}
  {tile(g, s) == T.Hint{} : T.Tile}

# LAW: "Once the game is over, no mine stays covered."
law display_mines:
  for w: Nat
  for h: Nat
  for layout: T.Grid(Bool)
  for shape: {shaped(Bool, w, h, layout) == True{} : Bool}
  for g: G.Game
  for r: Reachable(w, h, layout, g)
  for over: {G.status(g) != T.Playing{} : T.Status}
  for q: T.Pos
  for on: {on_board(w, h, q) == True{} : Bool}
  for m: {mine(layout, q) == True{} : Bool}
  {is_covered(tile(g, q)) == False{} : Bool}
