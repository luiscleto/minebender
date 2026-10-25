import Base
import ./types.bend as T

# Board helpers for the game. The ones named after a definition in LAWS.bend
# are copies of it (the code cannot import the laws), proven equal to it in
# the proofs.

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

def within_one(p: T.Pos, q: T.Pos) -> Bool:
  match p q:
    case T.Pos{px, py} T.Pos{qx, qy}:
      Nat.is_le(dist(px, qx), 1n) && Nat.is_le(dist(py, qy), 1n)

def adjacent(+p: T.Pos, +q: T.Pos) -> Bool:
  Bool.not(same(p, q)) && within_one(p, q)

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

def cells(w: Nat, h: Nat) -> List<&2, T.Pos>:
  cells.go(w, List.range(h))

def touching(+p: T.Pos, qs: List<&2, T.Pos>) -> List<&2, T.Pos>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> t:
      List.filter.put(T.Pos, q, touching(p, t), adjacent(p, q))

def neighbours(w: Nat, h: Nat, p: T.Pos) -> List<&2, T.Pos>:
  touching(p, cells(w, h))

def count_mines(+layout: T.Grid(Bool), ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case q <> t:
      Nat.add(Bool.pick(Nat, mine(layout, q), 1n, 0n), count_mines(layout, t))

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

def zero(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +p: T.Pos) -> Bool:
  on_board(w, h, p) && Bool.not(mine(layout, p))
    && Nat.is_eq(adj_mines(w, h, layout, p), 0n)

def rows_wide(-A: Data, +w: Nat, g: T.Grid(A)) -> Bool:
  match g:
    case Nil{}:
      True{}
    case r <> t:
      Nat.is_eq(List.length(&2, A, r), w) && rows_wide(A, w, t)

def shaped(-A: Data, w: Nat, h: Nat, +g: T.Grid(A)) -> Bool:
  Nat.is_eq(List.length(&2, List<&2, A>, g), h) && rows_wide(A, w, g)

# Game-only helpers
# -----------------

# The grid g with the cell at p replaced by v (unchanged when p is off it).
def set_at(-A: Data, +g: T.Grid(A), p: T.Pos, v: A) -> T.Grid(A):
  match p:
    case T.Pos{x, +y}:
      row = Maybe.default(&2, List<&2, A>, List.get(&2, List<&2, A>, g, y), Nil{})
      List.set(&2, List<&2, A>, g, y, List.set(&2, A, row, x, v))

# A w-by-h grid of v.
def blank(-A: Data, w: Nat, h: Nat, +v: A) -> T.Grid(A):
  List.replicate(List<&2, A>, h, List.replicate(A, w, v))

def row_false(row: List<&2, Bool>) -> Nat:
  match row:
    case Nil{}:
      0n
    case b <> t:
      Nat.add(Bool.pick(Nat, b, 0n, 1n), row_false(t))

# How many cells of the grid are False.
def count_false(g: T.Grid(Bool)) -> Nat:
  match g:
    case Nil{}:
      0n
    case r <> t:
      Nat.add(row_false(r), count_false(t))

def contains(xs: List<&2, T.Pos>, +p: T.Pos) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case q <> t:
      same(q, p) || contains(t, p)

def remove(xs: List<&2, T.Pos>, +p: T.Pos) -> List<&2, T.Pos>:
  match xs:
    case Nil{}:
      Nil{}
    case +q <> t:
      List.filter.put(T.Pos, q, remove(t, p), Bool.not(same(q, p)))
