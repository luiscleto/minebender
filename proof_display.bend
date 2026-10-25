import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG
import ./proof_copy.bend as PC
import ./proof_inv.bend as PI
import ./proof_laws.bend as PW

# Proofs of the display laws.

law disp_row_get:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +st: T.Status
  for +y: Nat
  for +xs: List<&2, Nat>
  for +j: Nat
  for +x: Nat
  for e: {List.get(&2, Nat, xs, j) == Some{x} : Maybe<&2, Nat>}
  {List.get(&2, T.Tile, G.disp_row(w, h, layout, shown, flags, st, y, xs), j)
    == Some{G.tile_at(w, h, layout, shown, flags, st, T.Pos{x, y})} : Maybe<&2, T.Tile>}

def disp_row_get(w, h, layout, shown, flags, st, y, xs, j, x, e):
  match xs j:
    case Nil{} _:
      Empty.absurd({List.get(&2, T.Tile, G.disp_row(w, h, layout, shown, flags, st, y, Nil{}), j)
        == Some{G.tile_at(w, h, layout, shown, flags, st, T.Pos{x, y})} : Maybe<&2, T.Tile>},
        PG.know_row_get.none(Nat, x, e))
    case a <> t 0n:
      %PG.know_row_get.some(Nat, a, x, e) :
        {Some{G.tile_at(w, h, layout, shown, flags, st, T.Pos{a, y})}
          == Some{G.tile_at(w, h, layout, shown, flags, st, T.Pos{_, y})} : Maybe<&2, T.Tile>}
      {==}
    case a <> t 1n+k:
      disp_row_get(w, h, layout, shown, flags, st, y, t, k, x, e)

law disp_rows_get:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +st: T.Status
  for +ys: List<&2, Nat>
  for +i: Nat
  for +y: Nat
  for e: {List.get(&2, Nat, ys, i) == Some{y} : Maybe<&2, Nat>}
  {List.get(&2, List<&2, T.Tile>, G.disp_rows(w, h, layout, shown, flags, st, ys), i)
    == Some{G.disp_row(w, h, layout, shown, flags, st, y, List.range(w))} : Maybe<&2, List<&2, T.Tile>>}

def disp_rows_get(w, h, layout, shown, flags, st, ys, i, y, e):
  match ys i:
    case Nil{} _:
      Empty.absurd({List.get(&2, List<&2, T.Tile>, G.disp_rows(w, h, layout, shown, flags, st, Nil{}), i)
        == Some{G.disp_row(w, h, layout, shown, flags, st, y, List.range(w))} : Maybe<&2, List<&2, T.Tile>>},
        PG.know_row_get.none(Nat, y, e))
    case a <> t 0n:
      %PG.know_row_get.some(Nat, a, y, e) :
        {Some{G.disp_row(w, h, layout, shown, flags, st, a, List.range(w))}
          == Some{G.disp_row(w, h, layout, shown, flags, st, _, List.range(w))} : Maybe<&2, List<&2, T.Tile>>}
      {==}
    case a <> t 1n+k:
      disp_rows_get(w, h, layout, shown, flags, st, t, k, y, e)

# On the board, the screen shows what tile_at says.
law disp_at:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +st: T.Status
  for +x: Nat
  for +y: Nat
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  {L.tile(G.Game{w, h, layout, shown, flags, st}, T.Pos{x, y}) == G.tile_at(w, h, layout, shown, flags, st, T.Pos{x, y}) : T.Tile}

def disp_at(w, h, layout, shown, flags, st, x, y, on):
  +xw = P.and_true_l(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +yh = P.and_true_r(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +rows = G.disp_rows(w, h, layout, shown, flags, st, List.range(h))
  +row = G.disp_row(w, h, layout, shown, flags, st, y, List.range(w))
  %Equal.sym(Maybe<&2, List<&2, T.Tile>>, List.get(&2, List<&2, T.Tile>, rows, y), Some{row},
    disp_rows_get(w, h, layout, shown, flags, st, List.range(h), y, y, P.range_get(h, y, yh))) :
    {Maybe.default(&2, T.Tile, List.get(&2, T.Tile, Maybe.default(&2, List<&2, T.Tile>, _, Nil{}), x), T.Covered{})
      == G.tile_at(w, h, layout, shown, flags, st, T.Pos{x, y}) : T.Tile}
  %Equal.sym(Maybe<&2, T.Tile>, List.get(&2, T.Tile, row, x), Some{G.tile_at(w, h, layout, shown, flags, st, T.Pos{x, y})},
    disp_row_get(w, h, layout, shown, flags, st, y, List.range(w), x, x, P.range_get(w, x, xw))) :
    {Maybe.default(&2, T.Tile, _, T.Covered{}) == G.tile_at(w, h, layout, shown, flags, st, T.Pos{x, y}) : T.Tile}
  {==}

# During play
# ===========

law play_cell:
  for +c: Bool
  for +m: Bool
  for +fl: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  {G.tile.go(None{}, c, m, fl, T.Playing{}, w, h, layout, p)
    == L.tile_of(G.seen_pick(c, m, w, h, layout, p), Bool.and(Bool.and(True{}, Bool.not(c)), fl)) : T.Tile}

def play_cell(c, m, fl, w, h, layout, p):
  match c m:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} _:
      {==}

law display_play_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +p: T.Pos
  for +on: {B.on_board(w, h, p) == True{} : Bool}
  {L.tile(G.Game{w, h, layout, s, f, T.Playing{}}, p)
    == L.tile_of(L.seen(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}), p), G.flagged(G.Game{w, h, layout, s, f, T.Playing{}}, p)) : T.Tile}

def display_play_c(w, h, layout, s, f, p, on):
  match p:
    case T.Pos{x, y}:
      +q = {T.Pos{x, y} : T.Pos}
      +g0 = {G.Game{w, h, layout, s, f, T.Playing{}} : G.Game}
      %Equal.sym(T.Tile, L.tile(g0, q), G.tile_at(w, h, layout, s, f, T.Playing{}, q),
        disp_at(w, h, layout, s, f, T.Playing{}, x, y, on)) :
        {_ == L.tile_of(L.seen(G.knowledge(g0), q), G.flagged(g0, q)) : T.Tile}
      %Equal.sym(T.Seen, L.seen(G.knowledge(g0), q), G.seen_at(w, h, layout, s, q),
        PW.know_seen(w, h, layout, s, f, T.Playing{}, q, on)) :
        {G.tile_at(w, h, layout, s, f, T.Playing{}, q) == L.tile_of(_, G.flagged(g0, q)) : T.Tile}
      %Equal.sym(Bool, B.on_board(w, h, q), True{}, on) :
        {G.tile_at(w, h, layout, s, f, T.Playing{}, q)
          == L.tile_of(G.seen_at(w, h, layout, s, q), Bool.and(Bool.and(_, Bool.not(B.at(Bool, False{}, s, q))), B.contains(f, q))) : T.Tile}
      play_cell(B.at(Bool, False{}, s, q), B.mine(layout, q), B.contains(f, q), w, h, layout, q)

# After the game
# ==============

law display_blast_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +p: T.Pos
  for +on: {B.on_board(w, h, p) == True{} : Bool}
  {L.tile(G.Game{w, h, layout, s, f, T.Lost{T.Exploded{p}}}, p) == T.Blast{} : T.Tile}

def display_blast_c(w, h, layout, s, f, p, on):
  match p:
    case T.Pos{x, y}:
      +q = {T.Pos{x, y} : T.Pos}
      %Equal.sym(T.Tile, L.tile(G.Game{w, h, layout, s, f, T.Lost{T.Exploded{q}}}, q),
        G.tile_at(w, h, layout, s, f, T.Lost{T.Exploded{q}}, q), disp_at(w, h, layout, s, f, T.Lost{T.Exploded{q}}, x, y, on)) :
        {_ == T.Blast{} : T.Tile}
      %Equal.sym(Bool, B.same(q, q), True{}, PG.same_refl(q)) :
        {G.tile.go(Bool.pick(Maybe<&2, T.Tile>, _, Some{T.Blast{}}, None{}), B.at(Bool, False{}, s, q), B.mine(layout, q),
          B.contains(f, q), T.Lost{T.Exploded{q}}, w, h, layout, q) == T.Blast{} : T.Tile}
      {==}

law display_hint_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +p: T.Pos
  for +on: {B.on_board(w, h, p) == True{} : Bool}
  {L.tile(G.Game{w, h, layout, s, f, T.Lost{T.AssistTooEarly{p}}}, p) == T.Hint{} : T.Tile}

def display_hint_c(w, h, layout, s, f, p, on):
  match p:
    case T.Pos{x, y}:
      +q = {T.Pos{x, y} : T.Pos}
      %Equal.sym(T.Tile, L.tile(G.Game{w, h, layout, s, f, T.Lost{T.AssistTooEarly{q}}}, q),
        G.tile_at(w, h, layout, s, f, T.Lost{T.AssistTooEarly{q}}, q), disp_at(w, h, layout, s, f, T.Lost{T.AssistTooEarly{q}}, x, y, on)) :
        {_ == T.Hint{} : T.Tile}
      %Equal.sym(Bool, B.same(q, q), True{}, PG.same_refl(q)) :
        {G.tile.go(Bool.pick(Maybe<&2, T.Tile>, _, Some{T.Hint{}}, None{}), B.at(Bool, False{}, s, q), B.mine(layout, q),
          B.contains(f, q), T.Lost{T.AssistTooEarly{q}}, w, h, layout, q) == T.Hint{} : T.Tile}
      {==}

# A mine, once the game is over, under each way the cell might be marked.
law over_cell:
  for +c: Bool
  for +st: T.Status
  for over: {st != T.Playing{} : T.Status}
  for +fl: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  {L.is_covered(G.tile.go(None{}, c, True{}, fl, st, w, h, layout, p)) == False{} : Bool}

def over_cell(c, st, over, fl, w, h, layout, p):
  match c:
    case True{}:
      {==}
    case False{}:
      match st:
        case T.Playing{}:
          Empty.absurd({L.is_covered(G.tile_hidden(T.Playing{}, True{}, fl)) == False{} : Bool}, over({==}))
        case T.Won{}:
          {==}
        case T.Lost{why}:
          match fl:
            case True{}:
              {==}
            case False{}:
              {==}

def mark_cell(+mk: Maybe<&2, T.Tile>, +c: Bool, +fl: Bool, +st: T.Status, over: {st != T.Playing{} : T.Status},
  +w: Nat, +h: Nat, +layout: T.Grid(Bool), +p: T.Pos,
  ok: {Maybe.default(&2, Bool, Maybe.map(&2, T.Tile, Bool, t => L.is_covered(t), mk), False{}) == False{} : Bool}) ->
  {L.is_covered(G.tile.go(mk, c, True{}, fl, st, w, h, layout, p)) == False{} : Bool}:
  match mk:
    case Some{t}:
      ok
    case None{}:
      over_cell(c, st, over, fl, w, h, layout, p)

def mark_ok.pick(+b: Bool, +t: T.Tile, ct: {L.is_covered(t) == False{} : Bool}) ->
  {Maybe.default(&2, Bool, Maybe.map(&2, T.Tile, Bool, x => L.is_covered(x), Bool.pick(Maybe<&2, T.Tile>, b, Some{t}, None{})), False{})
    == False{} : Bool}:
  match b:
    case True{}:
      ct
    case False{}:
      {==}

def mark_ok.why(+why: T.Loss, +p: T.Pos) ->
  {Maybe.default(&2, Bool, Maybe.map(&2, T.Tile, Bool, t => L.is_covered(t), G.mark.why(why, p)), False{}) == False{} : Bool}:
  match why:
    case T.Exploded{e}:
      mark_ok.pick(B.same(e, p), T.Blast{}, {==})
    case T.AssistTooEarly{s}:
      mark_ok.pick(B.same(s, p), T.Hint{}, {==})

# What the end of the game singles out is never covered.
law mark_ok:
  for +st: T.Status
  for +p: T.Pos
  {Maybe.default(&2, Bool, Maybe.map(&2, T.Tile, Bool, t => L.is_covered(t), G.mark(st, p)), False{}) == False{} : Bool}

def mark_ok(st, p):
  match st:
    case T.Playing{}:
      {==}
    case T.Won{}:
      {==}
    case T.Lost{why}:
      mark_ok.why(why, p)

law display_mines_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +st: T.Status
  for over: {st != T.Playing{} : T.Status}
  for +q: T.Pos
  for +on: {B.on_board(w, h, q) == True{} : Bool}
  for +m: {B.mine(layout, q) == True{} : Bool}
  {L.is_covered(L.tile(G.Game{w, h, layout, s, f, st}, q)) == False{} : Bool}

def display_mines_c(w, h, layout, s, f, st, over, q, on, m):
  match q:
    case T.Pos{x, y}:
      +p = {T.Pos{x, y} : T.Pos}
      %Equal.sym(T.Tile, L.tile(G.Game{w, h, layout, s, f, st}, p), G.tile_at(w, h, layout, s, f, st, p),
        disp_at(w, h, layout, s, f, st, x, y, on)) :
        {L.is_covered(_) == False{} : Bool}
      %Equal.sym(Bool, B.mine(layout, p), True{}, m) :
        {L.is_covered(G.tile.go(G.mark(st, p), B.at(Bool, False{}, s, p), _, B.contains(f, p), st, w, h, layout, p)) == False{} : Bool}
      mark_cell(G.mark(st, p), B.at(Bool, False{}, s, p), B.contains(f, p), st, over, w, h, layout, p, mark_ok(st, p))

# On real games
# =============

def on_conv(+w: Nat, +h: Nat, +p: T.Pos, on: {L.on_board(w, h, p) == True{} : Bool}) ->
  {B.on_board(w, h, p) == True{} : Bool}:
  %Equal.sym(Bool, B.on_board(w, h, p), L.on_board(w, h, p), PC.on_board_eq(w, h, p)) :
    {_ == True{} : Bool}; on

def display_play.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  +playing: {G.status(g) == T.Playing{} : T.Status}, +p: T.Pos, on: {L.on_board(w, h, p) == True{} : Bool},
  c: PW.Canon(w, h, layout, g)) ->
  {L.tile(g, p) == L.tile_of(L.seen(G.knowledge(g), p), G.flagged(g, p)) : T.Tile}:
  match c:
    case (eg, facts):
      +s = PW.shown_of(g)
      +f = PW.flags_of(g)
      %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
        {L.tile(_, p) == L.tile_of(L.seen(G.knowledge(_), p), G.flagged(_, p)) : T.Tile}
      %Equal.sym(T.Status, G.status(g), T.Playing{}, playing) :
        {L.tile(G.Game{w, h, layout, s, f, _}, p)
          == L.tile_of(L.seen(G.knowledge(G.Game{w, h, layout, s, f, _}), p), G.flagged(G.Game{w, h, layout, s, f, _}, p)) : T.Tile}
      display_play_c(w, h, layout, s, f, p, on_conv(w, h, p, on))

law display_play_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for +p: T.Pos
  for on: {L.on_board(w, h, p) == True{} : Bool}
  {L.tile(g, p) == L.tile_of(L.seen(G.knowledge(g), p), G.flagged(g, p)) : T.Tile}

def display_play_(w, h, layout, shape, g, r, playing, p, on):
  display_play.k(w, h, layout, g, playing, p, on, PW.canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

def display_blast.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game, +p: T.Pos,
  +lost: {G.status(g) == T.Lost{T.Exploded{p}} : T.Status}, on: {L.on_board(w, h, p) == True{} : Bool},
  c: PW.Canon(w, h, layout, g)) ->
  {L.tile(g, p) == T.Blast{} : T.Tile}:
  match c:
    case (eg, facts):
      +s = PW.shown_of(g)
      +f = PW.flags_of(g)
      %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
        {L.tile(_, p) == T.Blast{} : T.Tile}
      %Equal.sym(T.Status, G.status(g), T.Lost{T.Exploded{p}}, lost) :
        {L.tile(G.Game{w, h, layout, s, f, _}, p) == T.Blast{} : T.Tile}
      display_blast_c(w, h, layout, s, f, p, on_conv(w, h, p, on))

law display_blast_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +p: T.Pos
  for +lost: {G.status(g) == T.Lost{T.Exploded{p}} : T.Status}
  for on: {L.on_board(w, h, p) == True{} : Bool}
  {L.tile(g, p) == T.Blast{} : T.Tile}

def display_blast_(w, h, layout, shape, g, r, p, lost, on):
  display_blast.k(w, h, layout, g, p, lost, on, PW.canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

def display_hint.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game, +p: T.Pos,
  +lost: {G.status(g) == T.Lost{T.AssistTooEarly{p}} : T.Status}, on: {L.on_board(w, h, p) == True{} : Bool},
  c: PW.Canon(w, h, layout, g)) ->
  {L.tile(g, p) == T.Hint{} : T.Tile}:
  match c:
    case (eg, facts):
      +s = PW.shown_of(g)
      +f = PW.flags_of(g)
      %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
        {L.tile(_, p) == T.Hint{} : T.Tile}
      %Equal.sym(T.Status, G.status(g), T.Lost{T.AssistTooEarly{p}}, lost) :
        {L.tile(G.Game{w, h, layout, s, f, _}, p) == T.Hint{} : T.Tile}
      display_hint_c(w, h, layout, s, f, p, on_conv(w, h, p, on))

law display_hint_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +s: T.Pos
  for +lost: {G.status(g) == T.Lost{T.AssistTooEarly{s}} : T.Status}
  for on: {L.on_board(w, h, s) == True{} : Bool}
  {L.tile(g, s) == T.Hint{} : T.Tile}

def display_hint_(w, h, layout, shape, g, r, s, lost, on):
  display_hint.k(w, h, layout, g, s, lost, on, PW.canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

def display_mines.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  over: {G.status(g) != T.Playing{} : T.Status}, +q: T.Pos, on: {L.on_board(w, h, q) == True{} : Bool},
  m: {L.mine(layout, q) == True{} : Bool}, c: PW.Canon(w, h, layout, g)) ->
  {L.is_covered(L.tile(g, q)) == False{} : Bool}:
  match c:
    case (eg, facts):
      +s = PW.shown_of(g)
      +f = PW.flags_of(g)
      %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
        {L.is_covered(L.tile(_, q)) == False{} : Bool}
      display_mines_c(w, h, layout, s, f, G.status(g), over, q, on_conv(w, h, q, on),
        %Equal.sym(Bool, B.mine(layout, q), L.mine(layout, q), PC.mine_eq(layout, q)) :
          {_ == True{} : Bool}; m)

law display_mines_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for over: {G.status(g) != T.Playing{} : T.Status}
  for +q: T.Pos
  for on: {L.on_board(w, h, q) == True{} : Bool}
  for m: {L.mine(layout, q) == True{} : Bool}
  {L.is_covered(L.tile(g, q)) == False{} : Bool}

def display_mines_(w, h, layout, shape, g, r, over, q, on, m):
  display_mines.k(w, h, layout, g, over, q, on, m, PW.canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))
