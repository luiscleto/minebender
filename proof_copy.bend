import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G
import ./LAWS.bend as L
import ./proof_base.bend as P

# The game's copies of definitions in LAWS.bend equal the originals.

law at_eq:
  for -A: Data
  for +d: A
  for +g: T.Grid(A)
  for +p: T.Pos
  {B.at(A, d, g, p) == L.at(A, d, g, p) : A}

def at_eq(A, d, g, p):
  match p:
    case T.Pos{x, y}:
      {==}

law mine_eq:
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  {B.mine(layout, p) == L.mine(layout, p) : Bool}

def mine_eq(layout, p):
  match p:
    case T.Pos{x, y}:
      {==}

law on_board_eq:
  for +w: Nat
  for +h: Nat
  for +p: T.Pos
  {B.on_board(w, h, p) == L.on_board(w, h, p) : Bool}

def on_board_eq(w, h, p):
  match p:
    case T.Pos{x, y}:
      {==}

law same_eq:
  for +p: T.Pos
  for +q: T.Pos
  {B.same(p, q) == L.same(p, q) : Bool}

def same_eq(p, q):
  match p q:
    case T.Pos{px, py} T.Pos{qx, qy}:
      {==}

law adjacent_eq:
  for +p: T.Pos
  for +q: T.Pos
  {B.adjacent(p, q) == L.adjacent(p, q) : Bool}

def adjacent_eq(p, q):
  match p q:
    case T.Pos{px, py} T.Pos{qx, qy}:
      {==}

law row_cells_eq:
  for +y: Nat
  for +xs: List<&2, Nat>
  {B.row_cells(y, xs) == L.row_cells(y, xs) : List<&2, T.Pos>}

def row_cells_eq(y, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %row_cells_eq(y, t) : {T.Pos{x, y} <> B.row_cells(y, t) == T.Pos{x, y} <> _ : List<&2, T.Pos>}
      {==}

law cells_go_eq:
  for +w: Nat
  for +ys: List<&2, Nat>
  {B.cells.go(w, ys) == L.cells.go(w, ys) : List<&2, T.Pos>}

def cells_go_eq(w, ys):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      %row_cells_eq(y, List.range(w)) :
        {List.append(&2, T.Pos, B.row_cells(y, List.range(w)), B.cells.go(w, t))
          == List.append(&2, T.Pos, _, L.cells.go(w, t)) : List<&2, T.Pos>}
      %cells_go_eq(w, t) :
        {List.append(&2, T.Pos, B.row_cells(y, List.range(w)), B.cells.go(w, t))
          == List.append(&2, T.Pos, B.row_cells(y, List.range(w)), _) : List<&2, T.Pos>}
      {==}

law cells_eq:
  for +w: Nat
  for +h: Nat
  {B.cells(w, h) == L.cells(w, h) : List<&2, T.Pos>}

def cells_eq(w, h):
  cells_go_eq(w, List.range(h))

law touching_eq:
  for +p: T.Pos
  for +qs: List<&2, T.Pos>
  {B.touching(p, qs) == L.touching(p, qs) : List<&2, T.Pos>}

def touching_eq(p, qs):
  match qs:
    case Nil{}:
      {==}
    case q <> t:
      %adjacent_eq(p, q) :
        {List.filter.put(T.Pos, q, B.touching(p, t), B.adjacent(p, q))
          == List.filter.put(T.Pos, q, L.touching(p, t), _) : List<&2, T.Pos>}
      %touching_eq(p, t) :
        {List.filter.put(T.Pos, q, B.touching(p, t), B.adjacent(p, q))
          == List.filter.put(T.Pos, q, _, B.adjacent(p, q)) : List<&2, T.Pos>}
      {==}

law neighbours_eq:
  for +w: Nat
  for +h: Nat
  for +p: T.Pos
  {B.neighbours(w, h, p) == L.neighbours(w, h, p) : List<&2, T.Pos>}

def neighbours_eq(w, h, p):
  %cells_eq(w, h) : {B.touching(p, B.cells(w, h)) == L.touching(p, _) : List<&2, T.Pos>}
  touching_eq(p, B.cells(w, h))

law count_mines_eq:
  for +layout: T.Grid(Bool)
  for +ps: List<&2, T.Pos>
  {B.count_mines(layout, ps) == L.count_mines(layout, ps) : Nat}

def count_mines_eq(layout, ps):
  match ps:
    case Nil{}:
      {==}
    case q <> t:
      %mine_eq(layout, q) :
        {Nat.add(Bool.pick(Nat, B.mine(layout, q), 1n, 0n), B.count_mines(layout, t))
          == Nat.add(Bool.pick(Nat, _, 1n, 0n), L.count_mines(layout, t)) : Nat}
      %count_mines_eq(layout, t) :
        {Nat.add(Bool.pick(Nat, B.mine(layout, q), 1n, 0n), B.count_mines(layout, t))
          == Nat.add(Bool.pick(Nat, B.mine(layout, q), 1n, 0n), _) : Nat}
      {==}

law adj_mines_eq:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  {B.adj_mines(w, h, layout, p) == L.adj_mines(w, h, layout, p) : Nat}

def adj_mines_eq(w, h, layout, p):
  %neighbours_eq(w, h, p) :
    {B.count_mines(layout, B.neighbours(w, h, p)) == L.count_mines(layout, _) : Nat}
  count_mines_eq(layout, B.neighbours(w, h, p))

law row_mines_eq:
  for +row: List<&2, Bool>
  {B.row_mines(row) == L.row_mines(row) : Nat}

def row_mines_eq(row):
  match row:
    case Nil{}:
      {==}
    case b <> t:
      %row_mines_eq(t) :
        {Nat.add(Bool.pick(Nat, b, 1n, 0n), B.row_mines(t))
          == Nat.add(Bool.pick(Nat, b, 1n, 0n), _) : Nat}
      {==}

law total_mines_eq:
  for +layout: T.Grid(Bool)
  {B.total_mines(layout) == L.total_mines(layout) : Nat}

def total_mines_eq(layout):
  match layout:
    case Nil{}:
      {==}
    case r <> t:
      %row_mines_eq(r) :
        {Nat.add(B.row_mines(r), B.total_mines(t)) == Nat.add(_, L.total_mines(t)) : Nat}
      %total_mines_eq(t) :
        {Nat.add(B.row_mines(r), B.total_mines(t)) == Nat.add(B.row_mines(r), _) : Nat}
      {==}

law rows_wide_eq:
  for -A: Data
  for +w: Nat
  for +g: T.Grid(A)
  {B.rows_wide(A, w, g) == L.rows_wide(A, w, g) : Bool}

def rows_wide_eq(A, w, g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %rows_wide_eq(A, w, t) :
        {Bool.and(Nat.is_eq(List.length(&2, A, r), w), B.rows_wide(A, w, t))
          == Bool.and(Nat.is_eq(List.length(&2, A, r), w), _) : Bool}
      {==}

law shaped_eq:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  {B.shaped(A, w, h, g) == L.shaped(A, w, h, g) : Bool}

def shaped_eq(A, w, h, g):
  %rows_wide_eq(A, w, g) :
    {Bool.and(Nat.is_eq(List.length(&2, List<&2, A>, g), h), B.rows_wide(A, w, g))
      == Bool.and(Nat.is_eq(List.length(&2, List<&2, A>, g), h), _) : Bool}
  {==}

law zero_eq:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  {B.zero(w, h, layout, p) == L.zero(w, h, layout, p) : Bool}

def zero_eq(w, h, layout, p):
  +nz = Bool.and(Bool.not(B.mine(layout, p)), Nat.is_eq(B.adj_mines(w, h, layout, p), 0n))
  %on_board_eq(w, h, p) :
    {Bool.and(Bool.and(B.on_board(w, h, p), Bool.not(B.mine(layout, p))),
       Nat.is_eq(B.adj_mines(w, h, layout, p), 0n))
     == Bool.and(Bool.and(_, Bool.not(L.mine(layout, p))),
       Nat.is_eq(L.adj_mines(w, h, layout, p), 0n)) : Bool}
  %mine_eq(layout, p) :
    {Bool.and(Bool.and(B.on_board(w, h, p), Bool.not(B.mine(layout, p))),
       Nat.is_eq(B.adj_mines(w, h, layout, p), 0n))
     == Bool.and(Bool.and(B.on_board(w, h, p), Bool.not(_)),
       Nat.is_eq(L.adj_mines(w, h, layout, p), 0n)) : Bool}
  %adj_mines_eq(w, h, layout, p) :
    {Bool.and(Bool.and(B.on_board(w, h, p), Bool.not(B.mine(layout, p))),
       Nat.is_eq(B.adj_mines(w, h, layout, p), 0n))
     == Bool.and(Bool.and(B.on_board(w, h, p), Bool.not(B.mine(layout, p))),
       Nat.is_eq(_, 0n)) : Bool}
  {==}

law is_hidden_eq:
  for +s: T.Seen
  {G.is_hidden(s) == L.is_hidden(s) : Bool}

def is_hidden_eq(s):
  match s:
    case T.Hidden{}:
      {==}
    case T.Shown{k}:
      {==}
    case T.Boom{}:
      {==}

law seen_eq:
  for +v: T.Knowledge
  for +p: T.Pos
  {G.seen(v, p) == L.seen(v, p) : T.Seen}

def seen_eq(v, p):
  match v:
    case T.Knowledge{w, h, n, rows}:
      at_eq(T.Seen, T.Hidden{}, rows, p)

law hidden_eq:
  for +v: T.Knowledge
  for +p: T.Pos
  {G.hidden(v, p) == L.hidden(v, p) : Bool}

def hidden_eq(v, p):
  match v p:
    case T.Knowledge{w, h, n, rows} T.Pos{x, y}:
      %is_hidden_eq(B.at(T.Seen, T.Hidden{}, rows, T.Pos{x, y})) :
        {G.hidden(T.Knowledge{w, h, n, rows}, T.Pos{x, y})
          == Bool.and(B.on_board(w, h, T.Pos{x, y}), _) : Bool}
      {==}

law flags_among_eq:
  for +g: G.Game
  for +qs: List<&2, T.Pos>
  {G.flags_among(g, qs) == L.flags_among(g, qs) : Nat}

def flags_among_eq(g, qs):
  match qs:
    case Nil{}:
      {==}
    case q <> t:
      %flags_among_eq(g, t) :
        {Nat.add(Bool.pick(Nat, G.flagged(g, q), 1n, 0n), G.flags_among(g, t))
          == Nat.add(Bool.pick(Nat, G.flagged(g, q), 1n, 0n), _) : Nat}
      {==}

law hidden_unflagged_eq:
  for +g: G.Game
  for +v: T.Knowledge
  for +qs: List<&2, T.Pos>
  {G.hidden_unflagged(g, v, qs) == L.hidden_unflagged(g, v, qs) : List<&2, T.Pos>}

def hidden_unflagged_eq(g, v, qs):
  match qs:
    case Nil{}:
      {==}
    case q <> t:
      %hidden_eq(v, q) :
        {List.filter.put(T.Pos, q, G.hidden_unflagged(g, v, t),
          Bool.and(G.hidden(v, q), Bool.not(G.flagged(g, q))))
          == List.filter.put(T.Pos, q, L.hidden_unflagged(g, v, t),
          Bool.and(_, Bool.not(G.flagged(g, q)))) : List<&2, T.Pos>}
      %hidden_unflagged_eq(g, v, t) :
        {List.filter.put(T.Pos, q, G.hidden_unflagged(g, v, t),
          Bool.and(G.hidden(v, q), Bool.not(G.flagged(g, q))))
          == List.filter.put(T.Pos, q, _,
          Bool.and(G.hidden(v, q), Bool.not(G.flagged(g, q)))) : List<&2, T.Pos>}
      {==}

law chord_pick_eq:
  for +g: G.Game
  for +v: T.Knowledge
  for +ns: List<&2, T.Pos>
  for +s: T.Seen
  {G.chord_targets.pick(g, v, ns, s) == L.chord_targets.pick(g, v, ns, s) : List<&2, T.Pos>}

def chord_pick_eq(g, v, ns, s):
  match s:
    case T.Shown{k}:
      %flags_among_eq(g, ns) :
        {Bool.pick(List<&2, T.Pos>, Nat.is_eq(G.flags_among(g, ns), k),
          G.hidden_unflagged(g, v, ns), Nil{})
          == Bool.pick(List<&2, T.Pos>, Nat.is_eq(_, k),
          L.hidden_unflagged(g, v, ns), Nil{}) : List<&2, T.Pos>}
      %hidden_unflagged_eq(g, v, ns) :
        {Bool.pick(List<&2, T.Pos>, Nat.is_eq(G.flags_among(g, ns), k),
          G.hidden_unflagged(g, v, ns), Nil{})
          == Bool.pick(List<&2, T.Pos>, Nat.is_eq(G.flags_among(g, ns), k),
          _, Nil{}) : List<&2, T.Pos>}
      {==}
    case T.Hidden{}:
      {==}
    case T.Boom{}:
      {==}

def chord_targets_eq.go(+g: G.Game, +v: T.Knowledge, +p: T.Pos) ->
  {G.chord_targets.go(g, v, p) == L.chord_targets.go(g, v, p) : List<&2, T.Pos>}:
  match v:
    case T.Knowledge{w, h, n, rows}:
      +k = {T.Knowledge{w, h, n, rows} : T.Knowledge}
      %neighbours_eq(w, h, p) :
        {G.chord_targets.pick(g, k, B.neighbours(w, h, p), G.seen(k, p))
          == L.chord_targets.pick(g, k, _, L.seen(k, p)) : List<&2, T.Pos>}
      %seen_eq(k, p) :
        {G.chord_targets.pick(g, k, B.neighbours(w, h, p), G.seen(k, p))
          == L.chord_targets.pick(g, k, B.neighbours(w, h, p), _) : List<&2, T.Pos>}
      chord_pick_eq(g, k, B.neighbours(w, h, p), G.seen(k, p))

law chord_targets_eq:
  for +g: G.Game
  for +p: T.Pos
  {G.chord_targets(g, p) == L.chord_targets(g, p) : List<&2, T.Pos>}

def chord_targets_eq(g, p):
  chord_targets_eq.go(g, G.knowledge(g), p)

