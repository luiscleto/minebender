import Base
import ./types.bend as T
import ./board.bend as B
import ./solver.bend as S

# The game. LAWS.bend states what it must do; PROOF.bend proves it does.

# The real mines, the cells revealed so far, the player's flags (any cells;
# only hidden ones count as flagged) and the status.
type Game is Data:
  Game{w: Nat, h: Nat, layout: T.Grid(Bool), shown: T.Grid(Bool),
    flags: List<&2, T.Pos>, status: T.Status}

# Accessors
# ---------

def status(g: Game) -> T.Status:
  match g:
    case Game{w, h, layout, shown, flags, status}:
      status

def is_playing(s: T.Status) -> Bool:
  match s:
    case T.Playing{}:
      True{}
    case o:
      False{}

# p is a cell of the board that is not revealed yet.
def unrevealed(+w: Nat, +h: Nat, shown: T.Grid(Bool), +p: T.Pos) -> Bool:
  B.on_board(w, h, p) && Bool.not(B.at(Bool, False{}, shown, p))

def flagged(g: Game, +p: T.Pos) -> Bool:
  match g:
    case Game{w, h, layout, shown, flags, status}:
      unrevealed(w, h, shown, p) && B.contains(flags, p)

# What the player sees at p.
def seen_pick(s: Bool, m: Bool, w: Nat, h: Nat, layout: T.Grid(Bool), p: T.Pos) -> T.Seen:
  match s m:
    case False{} _:
      T.Hidden{}
    case True{} True{}:
      T.Boom{}
    case True{} False{}:
      T.Shown{B.adj_mines(w, h, layout, p)}

def seen_at(+w: Nat, +h: Nat, +layout: T.Grid(Bool), shown: T.Grid(Bool), +p: T.Pos) -> T.Seen:
  seen_pick(B.at(Bool, False{}, shown, p), B.mine(layout, p), w, h, layout, p)

def know_row(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +y: Nat,
  xs: List<&2, Nat>) -> List<&2, T.Seen>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      seen_at(w, h, layout, shown, T.Pos{x, y}) <> know_row(w, h, layout, shown, y, t)

def know_rows(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool),
  ys: List<&2, Nat>) -> T.Grid(T.Seen):
  match ys:
    case Nil{}:
      Nil{}
    case y <> t:
      know_row(w, h, layout, shown, y, List.range(w)) <> know_rows(w, h, layout, shown, t)

def knowledge(g: Game) -> T.Knowledge:
  match g:
    case Game{+w, +h, +layout, shown, flags, status}:
      T.Knowledge{w, h, B.total_mines(layout), know_rows(w, h, layout, shown, List.range(h))}

# Every safe cell is revealed.
def all_safe.go(+layout: T.Grid(Bool), +shown: T.Grid(Bool), ps: List<&2, T.Pos>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> t:
      (B.mine(layout, p) || B.at(Bool, False{}, shown, p)) && all_safe.go(layout, shown, t)

def all_safe(w: Nat, h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool)) -> Bool:
  all_safe.go(layout, shown, B.cells(w, h))

def won_or_playing(b: Bool) -> T.Status:
  match b:
    case True{}:
      T.Won{}
    case False{}:
      T.Playing{}

# Starting and setting up
# -----------------------

def fresh(+w: Nat, +h: Nat, +layout: T.Grid(Bool)) -> Game:
  +shown = B.blank(Bool, w, h, False{})
  Game{w, h, layout, shown, Nil{}, won_or_playing(all_safe(w, h, layout, shown))}

def clamp(lo: Nat, hi: Nat, x: Nat) -> Nat:
  Nat.max(lo, Nat.min(hi, x))

def custom(w: Nat, h: Nat, m: Nat) -> T.Setup:
  +cw = clamp(9n, 30n, w)
  +ch = clamp(9n, 25n, h)
  T.Setup{cw, ch, Nat.min(clamp(10n, 999n, m), Nat.sub(Nat.mul(cw, ch), 10n))}

def setup(l: T.Level) -> T.Setup:
  match l:
    case T.Beginner{}:
      T.Setup{9n, 9n, 10n}
    case T.Intermediate{}:
      T.Setup{16n, 16n, 40n}
    case T.Expert{}:
      T.Setup{30n, 16n, 99n}
    case T.Custom{w, h, m}:
      custom(w, h, m)

# Board generation
# ----------------
# Selection sampling (Knuth's Algorithm S) over the cells outside a zone
# kept free, row by row: with `need` mines still to place among `left`
# candidates, a cell gets a mine when need = left, or else with probability
# about need/left. Whatever the random numbers, exactly n mines come out.
#
# The zone is the first click and, when there is room, its neighbours too,
# so the first click opens an area (as in Windows Vista and later).

# The cells kept free of mines: `first`, and its neighbours when `wide`.
type Zone is Data:
  Zone{first: T.Pos, wide: Bool}

def gen.out(z: Zone, +p: T.Pos) -> Bool:
  match z:
    case Zone{+first, wide}:
      Bool.pick(Bool, wide, B.within_one(first, p), B.same(p, first))

type GenState is Data:
  GenState{need: Nat, left: Nat, rs: List<&2, U32>}

def gen.coin(r: U32, +left: Nat, need: Nat) -> Bool:
  Nat.is_lt(Nat.mod(U32.to_nat(r), left), need)

# Whether the next candidate gets a mine: forced when every candidate left
# needs one, else a coin flip that comes up heads about need/left of the time.
def gen.pick(+need: Nat, +left: Nat, rs: List<&2, U32>) -> Bool:
  match rs:
    case Nil{}:
      Nat.is_eq(need, left)
    case r <> t:
      Nat.is_eq(need, left) || gen.coin(r, left, need)

# Whether cell p gets a mine.
def gen.bit(z: Zone, p: T.Pos, st: GenState) -> Bool:
  match st:
    case GenState{+need, left, rs}:
      Bool.not(gen.out(z, p)) && Nat.is_lt(0n, need) && gen.pick(need, left, rs)

def gen.next.go(skip: Bool, bit: Bool, need: Nat, left: Nat, rs: List<&2, U32>) -> GenState:
  match skip:
    case True{}:
      GenState{need, left, rs}
    case False{}:
      GenState{Nat.sub(need, Bool.pick(Nat, bit, 1n, 0n)), Nat.sub(left, 1n),
        List.tail(&2, U32, rs)}

# The state after cell p.
def gen.next(+z: Zone, +p: T.Pos, +st: GenState) -> GenState:
  match st:
    case GenState{need, left, rs}:
      gen.next.go(gen.out(z, p), gen.bit(z, p, st), need, left, rs)

def gen.row(+z: Zone, +y: Nat, xs: List<&2, Nat>, +st: GenState) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      +p = {T.Pos{x, y} : T.Pos}
      gen.bit(z, p, st) <> gen.row(z, y, t, gen.next(z, p, st))

# The state after a row.
def gen.row_state(+z: Zone, +y: Nat, xs: List<&2, Nat>, +st: GenState) -> GenState:
  match xs:
    case Nil{}:
      st
    case x <> t:
      gen.row_state(z, y, t, gen.next(z, T.Pos{x, y}, st))

def gen.rows(+z: Zone, +w: Nat, ys: List<&2, Nat>, +st: GenState) -> T.Grid(Bool):
  match ys:
    case Nil{}:
      Nil{}
    case +y <> t:
      gen.row(z, y, List.range(w), st)
        <> gen.rows(z, w, t, gen.row_state(z, y, List.range(w), st))

# How many cells of ps are outside the zone.
def gen.left(+z: Zone, ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> t:
      Nat.add(Bool.pick(Nat, gen.out(z, p), 0n, 1n), gen.left(z, t))

# Room for the first click's neighbours: at least 9 cells left free.
def place_mines(+w: Nat, +h: Nat, +n: Nat, +first: T.Pos, rs: List<&2, U32>) -> T.Grid(Bool):
  +z = {Zone{first, Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h))} : Zone}
  gen.rows(z, w, List.range(h), GenState{n, gen.left(z, B.cells(w, h)), rs})

# Revealing
# ---------

# A cell queued by the flood, with the path that reached it from the cell
# first opened, newest step first (kept only so the proofs can name it).
type Work is Data:
  Work{c: T.Pos, back: List<&2, T.Pos>}

# The first cell of `work` is on the board and not revealed yet.
def head_hidden(+w: Nat, +h: Nat, shown: T.Grid(Bool), work: List<&2, Work>) -> Bool:
  match work:
    case Nil{}:
      False{}
    case Work{c, back} <> t:
      unrevealed(w, h, shown, c)

# The cells ns, each reached one step past `back`.
def works(ns: List<&2, T.Pos>, +back: List<&2, T.Pos>) -> List<&2, Work>:
  match ns:
    case Nil{}:
      Nil{}
    case +r <> t:
      Work{r, r <> back} <> works(t, back)

def push(z: Bool, ns: List<&2, T.Pos>, back: List<&2, T.Pos>, rest: List<&2, Work>) ->
  List<&2, Work>:
  match z:
    case True{}:
      List.append(&2, Work, works(ns, back), rest)
    case False{}:
      rest

# Reveal the cells of `work`, and the neighbours of every zero revealed. n is
# how many cells are not revealed yet: each reveal uses one up.
def flood(+n: Nat, work: List<&2, Work>, hd: Bool, +w: Nat, +h: Nat,
  +layout: T.Grid(Bool), +shown: T.Grid(Bool)) -> T.Grid(Bool):
  match n:
    case 0n:
      shown
    case 1n+m:
      match work:
        case Nil{}:
          shown
        case Work{+c, +back} <> +rest:
          match hd:
            case False{}:
              flood(n, rest, head_hidden(w, h, shown, rest), w, h, layout, shown)
            case True{}:
              +sh = B.set_at(Bool, shown, c, True{})
              +wk = push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest)
              flood(m, wk, head_hidden(w, h, sh, wk), w, h, layout, sh)

def explode(g: Game, +p: T.Pos) -> Game:
  match g:
    case Game{w, h, layout, shown, flags, status}:
      Game{w, h, layout, B.set_at(Bool, shown, p, True{}), flags, T.Lost{T.Exploded{p}}}

def flood_open(g: Game, +p: T.Pos) -> Game:
  match g:
    case Game{+w, +h, +layout, +shown, flags, status}:
      +start = {[Work{p, Nil{}}] : List<&2, Work>}
      +sh = flood(B.count_false(shown), start, head_hidden(w, h, shown, start), w, h, layout, shown)
      Game{w, h, layout, sh, flags, won_or_playing(all_safe(w, h, layout, sh))}

def open.go(can: Bool, boom: Bool, g: Game, p: T.Pos) -> Game:
  match can boom:
    case False{} _:
      g
    case True{} True{}:
      explode(g, p)
    case True{} False{}:
      flood_open(g, p)

# During play, a hidden cell of the board can be opened.
def can_open(g: Game, +p: T.Pos) -> Bool:
  match g:
    case Game{w, h, layout, shown, flags, status}:
      is_playing(status) && unrevealed(w, h, shown, p)

def layout_of(g: Game) -> T.Grid(Bool):
  match g:
    case Game{w, h, layout, shown, flags, status}:
      layout

# Reveal p whether or not it is flagged (Reveal, Chord and Assist use it).
def open(+g: Game, +p: T.Pos) -> Game:
  open.go(can_open(g, p), B.mine(layout_of(g), p), g, p)

def reveal.go(f: Bool, g: Game, p: T.Pos) -> Game:
  match f:
    case True{}:
      g
    case False{}:
      open(g, p)

def reveal(+g: Game, +p: T.Pos) -> Game:
  reveal.go(flagged(g, p), g, p)

# Chording
# --------

def flags_among(+g: Game, qs: List<&2, T.Pos>) -> Nat:
  match qs:
    case Nil{}:
      0n
    case q <> t:
      Nat.add(Bool.pick(Nat, flagged(g, q), 1n, 0n), flags_among(g, t))

def is_hidden(s: T.Seen) -> Bool:
  match s:
    case T.Hidden{}:
      True{}
    case o:
      False{}

def hidden(v: T.Knowledge, +p: T.Pos) -> Bool:
  match v:
    case T.Knowledge{w, h, n, rows}:
      B.on_board(w, h, p) && is_hidden(B.at(T.Seen, T.Hidden{}, rows, p))

def seen(v: T.Knowledge, p: T.Pos) -> T.Seen:
  match v:
    case T.Knowledge{w, h, n, rows}:
      B.at(T.Seen, T.Hidden{}, rows, p)

def hidden_unflagged(+g: Game, +v: T.Knowledge, qs: List<&2, T.Pos>) -> List<&2, T.Pos>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> t:
      List.filter.put(T.Pos, q, hidden_unflagged(g, v, t),
        hidden(v, q) && Bool.not(flagged(g, q)))

def chord_targets.pick(+g: Game, v: T.Knowledge, +ns: List<&2, T.Pos>, s: T.Seen) ->
  List<&2, T.Pos>:
  match s:
    case T.Shown{k}:
      Bool.pick(List<&2, T.Pos>, Nat.is_eq(flags_among(g, ns), k),
        hidden_unflagged(g, v, ns), Nil{})
    case o:
      Nil{}

def chord_targets.go(g: Game, +v: T.Knowledge, +p: T.Pos) -> List<&2, T.Pos>:
  match v:
    case T.Knowledge{w, h, n, rows}:
      chord_targets.pick(g, v, B.neighbours(w, h, p), seen(v, p))

def chord_targets(+g: Game, p: T.Pos) -> List<&2, T.Pos>:
  chord_targets.go(g, knowledge(g), p)

def chord_play(ts: List<&2, T.Pos>, g: Game) -> Game:
  match ts:
    case Nil{}:
      g
    case q <> t:
      chord_play(t, reveal(g, q))

# Flags
# -----

def toggle.go(has: Bool, flags: List<&2, T.Pos>, +p: T.Pos) -> List<&2, T.Pos>:
  match has:
    case True{}:
      B.remove(flags, p)
    case False{}:
      p <> flags

def toggle(+flags: List<&2, T.Pos>, +p: T.Pos) -> List<&2, T.Pos>:
  toggle.go(B.contains(flags, p), flags, p)

def flag.go(c: Bool, g: Game, p: T.Pos) -> Game:
  match c:
    case False{}:
      g
    case True{}:
      match g:
        case Game{w, h, layout, shown, flags, status}:
          Game{w, h, layout, shown, toggle(flags, p), status}

def can_flag(g: Game, +p: T.Pos) -> Bool:
  match g:
    case Game{w, h, layout, shown, flags, status}:
      is_playing(status) && unrevealed(w, h, shown, p)

def flag(+g: Game, +p: T.Pos) -> Game:
  flag.go(can_flag(g, p), g, p)

# The assist
# ----------

# The first cell of ps is safe and not revealed yet.
def safe_here(+layout: T.Grid(Bool), +shown: T.Grid(Bool), ps: List<&2, T.Pos>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> t:
      Bool.not(B.mine(layout, p)) && Bool.not(B.at(Bool, False{}, shown, p))

def first_safe.go(ps: List<&2, T.Pos>, hit: Bool, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool)) -> Maybe<&2, T.Pos>:
  match ps:
    case Nil{}:
      None{}
    case p <> +t:
      match hit:
        case True{}:
          Some{p}
        case False{}:
          first_safe.go(t, safe_here(layout, shown, t), layout, shown)

# The first safe cell of ps that is not revealed yet.
def first_safe(+layout: T.Grid(Bool), +shown: T.Grid(Bool), +ps: List<&2, T.Pos>) ->
  Maybe<&2, T.Pos>:
  first_safe.go(ps, safe_here(layout, shown, ps), layout, shown)

def any_shown(+shown: T.Grid(Bool), ps: List<&2, T.Pos>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      B.at(Bool, False{}, shown, p) || any_shown(shown, t)

# The cells of ps not revealed yet but next to a revealed one.
def edges(+w: Nat, +h: Nat, +shown: T.Grid(Bool), ps: List<&2, T.Pos>) -> List<&2, T.Pos>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      List.filter.put(T.Pos, p, edges(w, h, shown, t),
        Bool.not(B.at(Bool, False{}, shown, p)) && any_shown(shown, B.neighbours(w, h, p)))

# ps from a point picked by k, wrapping around.
def turn(+ps: List<&2, T.Pos>, +k: Nat) -> List<&2, T.Pos>:
  +i = Nat.mod(k, Nat.add(List.length(&2, T.Pos, ps), 1n))
  List.append(&2, T.Pos, List.drop(&2, T.Pos, ps, i), List.take(&2, T.Pos, ps, i))

# Where the assist looks for a safe cell, k being a random number: first
# the hidden cells next to a revealed one, then every cell, each from a
# random point; last every cell in order, which never comes into play but
# lets the proofs see a safe cell is always found.
def safe_list(+w: Nat, +h: Nat, +shown: T.Grid(Bool), +k: Nat) -> List<&2, T.Pos>:
  +cs = B.cells(w, h)
  List.append(&2, T.Pos, turn(edges(w, h, shown, cs), k), List.append(&2, T.Pos, turn(cs, k), cs))

def safe_cell(g: Game, +k: Nat) -> Maybe<&2, T.Pos>:
  match g:
    case Game{+w, +h, +layout, +shown, flags, status}:
      first_safe(layout, shown, safe_list(w, h, shown, k))

def lose(g: Game, p: T.Pos) -> Game:
  match g:
    case Game{w, h, layout, shown, flags, status}:
      Game{w, h, layout, shown, flags, T.Lost{T.AssistTooEarly{p}}}

def assist.safe(m: Maybe<&2, T.Pos>, g: Game) -> Game:
  match m:
    case None{}:
      g
    case Some{p}:
      open(g, p)

def assist.pick(r: Maybe<&2, T.Pos>, +g: Game, +k: Nat) -> Game:
  match r:
    case Some{q}:
      lose(g, q)
    case None{}:
      assist.safe(safe_cell(g, k), g)

def assist.go(playing: Bool, +g: Game, +k: Nat) -> Game:
  match playing:
    case False{}:
      g
    case True{}:
      assist.pick(S.solve(knowledge(g)), g, k)

def assist(+g: Game, +k: Nat) -> Game:
  assist.go(is_playing(status(g)), g, k)

# Actions
# -------

def step(+g: Game, a: T.Action) -> Game:
  match a:
    case T.Reveal{p}:
      reveal(g, p)
    case T.Chord{p}:
      chord_play(chord_targets(g, p), g)
    case T.Flag{p}:
      flag(g, p)
    case T.Assist{k}:
      assist(g, k)

# The display
# -----------
# What every cell looks like on screen. During play it shows exactly what the
# player knows, plus their flags. Once the game is over it also shows the
# mines, like Windows: the mine that exploded, every other mine, crosses on
# wrong flags, and (after an assist pressed too early) the safe cell missed.

def mark.why(why: T.Loss, +p: T.Pos) -> Maybe<&2, T.Tile>:
  match why:
    case T.Exploded{e}:
      Bool.pick(Maybe<&2, T.Tile>, B.same(e, p), Some{T.Blast{}}, None{})
    case T.AssistTooEarly{s}:
      Bool.pick(Maybe<&2, T.Tile>, B.same(s, p), Some{T.Hint{}}, None{})

# A cell the end of the game singles out.
def mark(st: T.Status, +p: T.Pos) -> Maybe<&2, T.Tile>:
  match st:
    case T.Lost{why}:
      mark.why(why, p)
    case o:
      None{}

def tile_lost(m: Bool, f: Bool) -> T.Tile:
  match m f:
    case True{} True{}:
      T.Flagged{}
    case True{} False{}:
      T.Mine{}
    case False{} True{}:
      T.BadFlag{}
    case False{} False{}:
      T.Covered{}

def tile_hidden(st: T.Status, m: Bool, f: Bool) -> T.Tile:
  match st:
    case T.Playing{}:
      Bool.pick(T.Tile, f, T.Flagged{}, T.Covered{})
    case T.Won{}:
      Bool.pick(T.Tile, m, T.Flagged{}, T.Covered{})
    case T.Lost{why}:
      tile_lost(m, f)

def tile_shown(m: Bool, w: Nat, h: Nat, layout: T.Grid(Bool), p: T.Pos) -> T.Tile:
  match m:
    case True{}:
      T.Blast{}
    case False{}:
      T.Number{B.adj_mines(w, h, layout, p)}

def tile.go(mk: Maybe<&2, T.Tile>, s: Bool, m: Bool, f: Bool, st: T.Status, w: Nat, h: Nat,
  layout: T.Grid(Bool), p: T.Pos) -> T.Tile:
  match mk:
    case Some{t}:
      t
    case None{}:
      match s:
        case True{}:
          tile_shown(m, w, h, layout, p)
        case False{}:
          tile_hidden(st, m, f)

def tile_at(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +st: T.Status, +p: T.Pos) -> T.Tile:
  tile.go(mark(st, p), B.at(Bool, False{}, shown, p), B.mine(layout, p), B.contains(flags, p), st, w, h, layout, p)

def disp_row(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +st: T.Status, +y: Nat, xs: List<&2, Nat>) -> List<&2, T.Tile>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      tile_at(w, h, layout, shown, flags, st, T.Pos{x, y}) <> disp_row(w, h, layout, shown, flags, st, y, t)

def disp_rows(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +st: T.Status, ys: List<&2, Nat>) -> T.Grid(T.Tile):
  match ys:
    case Nil{}:
      Nil{}
    case y <> t:
      disp_row(w, h, layout, shown, flags, st, y, List.range(w)) <> disp_rows(w, h, layout, shown, flags, st, t)

def display(g: Game) -> T.Grid(T.Tile):
  match g:
    case Game{+w, +h, +layout, +shown, +flags, +status}:
      disp_rows(w, h, layout, shown, flags, status, List.range(h))

# How many flags the mine counter shows: the mines, less the flags placed.
def flags_shown(+w: Nat, +h: Nat, +shown: T.Grid(Bool), flags: List<&2, T.Pos>) -> Nat:
  match flags:
    case Nil{}:
      0n
    case +p <> t:
      Nat.add(Bool.pick(Nat, unrevealed(w, h, shown, p), 1n, 0n), flags_shown(w, h, shown, t))
