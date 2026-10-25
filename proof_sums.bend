import Base
import ./types.bend as T
import ./board.bend as B
import ./proof_base.bend as P
import ./proof_lists.bend as PL

# Summing a value over a grid, row by row, equals summing it over the
# board's cells, cell by cell.

# Each element plus one.
def smap(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      (1n+x) <> smap(t)

law map_append:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  {smap(List.append(&2, Nat, xs, ys))
    == List.append(&2, Nat, smap(xs), smap(ys)) : List<&2, Nat>}

def map_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(List<&2, Nat>, smap(List.append(&2, Nat, t, ys)),
        List.append(&2, Nat, smap(t), smap(ys)), map_append(t, ys)) :
        {(1n+x) <> _ == (1n+x) <> List.append(&2, Nat, smap(t), smap(ys))
          : List<&2, Nat>}
      {==}

# range(1+n) is 0 followed by 1..n.
law range_cons:
  for +n: Nat
  {List.range(1n+n) == 0n <> smap(List.range(n)) : List<&2, Nat>}

def range_cons(n):
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(List<&2, Nat>, List.range(2n+m), List.append(&2, Nat, List.range(1n+m), [1n+m]), P.range_snoc(1n+m)) :
        {_ == 0n <> smap(List.range(1n+m)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.range(1n+m), 0n <> smap(List.range(m)), range_cons(m)) :
        {List.append(&2, Nat, _, [1n+m]) == 0n <> smap(List.range(1n+m)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.range(1n+m), List.append(&2, Nat, List.range(m), [m]), P.range_snoc(m)) :
        {List.append(&2, Nat, 0n <> smap(List.range(m)), [1n+m]) == 0n <> smap(_) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, smap(List.append(&2, Nat, List.range(m), [m])),
        List.append(&2, Nat, smap(List.range(m)), smap([m])), map_append(List.range(m), [m])) :
        {List.append(&2, Nat, 0n <> smap(List.range(m)), [1n+m]) == 0n <> _ : List<&2, Nat>}
      {==}

def rsum(~A: Data, ~f: A -> Nat, r: List<&2, A>) -> Nat:
  match r:
    case Nil{}:
      0n
    case a <> t:
      Nat.add(f(a), rsum(~A, ~f, t))

# The sum of f over the grid, row by row.
def gsum(~A: Data, ~f: A -> Nat, g: T.Grid(A)) -> Nat:
  match g:
    case Nil{}:
      0n
    case r <> t:
      Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, t))

# The sum of f over the cells ps of the grid.
def csum(~A: Data, ~f: A -> Nat, +d: A, +g: T.Grid(A), ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case q <> t:
      Nat.add(f(B.at(A, d, g, q)), csum(~A, ~f, d, g, t))

def rsum_at(~A: Data, ~f: A -> Nat, +d: A, +r: List<&2, A>, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(f(Maybe.default(&2, A, List.get(&2, A, r, x), d)), rsum_at(~A, ~f, d, r, t))

law csum_append:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +g: T.Grid(A)
  for +xs: List<&2, T.Pos>
  for +ys: List<&2, T.Pos>
  {csum(~A, ~f, d, g, List.append(&2, T.Pos, xs, ys)) == Nat.add(csum(~A, ~f, d, g, xs), csum(~A, ~f, d, g, ys)) : Nat}

def csum_append(A, f, d, g, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case q <> t:
      %Equal.sym(Nat, csum(~A, ~f, d, g, List.append(&2, T.Pos, t, ys)),
        Nat.add(csum(~A, ~f, d, g, t), csum(~A, ~f, d, g, ys)), csum_append(~A, ~f, d, g, t, ys)) :
        {Nat.add(f(B.at(A, d, g, q)), _) == Nat.add(Nat.add(f(B.at(A, d, g, q)), csum(~A, ~f, d, g, t)), csum(~A, ~f, d, g, ys)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(f(B.at(A, d, g, q)), csum(~A, ~f, d, g, t)), csum(~A, ~f, d, g, ys)),
        Nat.add(f(B.at(A, d, g, q)), Nat.add(csum(~A, ~f, d, g, t), csum(~A, ~f, d, g, ys))),
        P.add_assoc(f(B.at(A, d, g, q)), csum(~A, ~f, d, g, t), csum(~A, ~f, d, g, ys)))

law csum_row0:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +r: List<&2, A>
  for +rt: T.Grid(A)
  for +xs: List<&2, Nat>
  {csum(~A, ~f, d, r <> rt, B.row_cells(0n, xs)) == rsum_at(~A, ~f, d, r, xs) : Nat}

def csum_row0(A, f, d, r, rt, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Nat, csum(~A, ~f, d, r <> rt, B.row_cells(0n, t)), rsum_at(~A, ~f, d, r, t), csum_row0(~A, ~f, d, r, rt, t)) :
        {Nat.add(f(Maybe.default(&2, A, List.get(&2, A, r, x), d)), _)
          == Nat.add(f(Maybe.default(&2, A, List.get(&2, A, r, x), d)), rsum_at(~A, ~f, d, r, t)) : Nat}
      {==}

law csum_row_shift:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +r: List<&2, A>
  for +rt: T.Grid(A)
  for +y: Nat
  for +xs: List<&2, Nat>
  {csum(~A, ~f, d, r <> rt, B.row_cells(1n+y, xs)) == csum(~A, ~f, d, rt, B.row_cells(y, xs)) : Nat}

def csum_row_shift(A, f, d, r, rt, y, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Nat, csum(~A, ~f, d, r <> rt, B.row_cells(1n+y, t)), csum(~A, ~f, d, rt, B.row_cells(y, t)),
        csum_row_shift(~A, ~f, d, r, rt, y, t)) :
        {Nat.add(f(B.at(A, d, rt, T.Pos{x, y})), _) == Nat.add(f(B.at(A, d, rt, T.Pos{x, y})), csum(~A, ~f, d, rt, B.row_cells(y, t))) : Nat}
      {==}

law csum_shift:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +r: List<&2, A>
  for +rt: T.Grid(A)
  for +w: Nat
  for +ys: List<&2, Nat>
  {csum(~A, ~f, d, r <> rt, B.cells.go(w, smap(ys))) == csum(~A, ~f, d, rt, B.cells.go(w, ys)) : Nat}

def csum_shift(A, f, d, r, rt, w, ys):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +g = {r <> rt : T.Grid(A)}
      %Equal.sym(Nat, csum(~A, ~f, d, g, List.append(&2, T.Pos, B.row_cells(1n+y, List.range(w)), B.cells.go(w, smap(t)))),
        Nat.add(csum(~A, ~f, d, g, B.row_cells(1n+y, List.range(w))), csum(~A, ~f, d, g, B.cells.go(w, smap(t)))),
        csum_append(~A, ~f, d, g, B.row_cells(1n+y, List.range(w)), B.cells.go(w, smap(t)))) :
        {_ == csum(~A, ~f, d, rt, List.append(&2, T.Pos, B.row_cells(y, List.range(w)), B.cells.go(w, t))) : Nat}
      %Equal.sym(Nat, csum(~A, ~f, d, rt, List.append(&2, T.Pos, B.row_cells(y, List.range(w)), B.cells.go(w, t))),
        Nat.add(csum(~A, ~f, d, rt, B.row_cells(y, List.range(w))), csum(~A, ~f, d, rt, B.cells.go(w, t))),
        csum_append(~A, ~f, d, rt, B.row_cells(y, List.range(w)), B.cells.go(w, t))) :
        {Nat.add(csum(~A, ~f, d, g, B.row_cells(1n+y, List.range(w))), csum(~A, ~f, d, g, B.cells.go(w, smap(t)))) == _ : Nat}
      %Equal.sym(Nat, csum(~A, ~f, d, g, B.row_cells(1n+y, List.range(w))), csum(~A, ~f, d, rt, B.row_cells(y, List.range(w))),
        csum_row_shift(~A, ~f, d, r, rt, y, List.range(w))) :
        {Nat.add(_, csum(~A, ~f, d, g, B.cells.go(w, smap(t))))
          == Nat.add(csum(~A, ~f, d, rt, B.row_cells(y, List.range(w))), csum(~A, ~f, d, rt, B.cells.go(w, t))) : Nat}
      %Equal.sym(Nat, csum(~A, ~f, d, g, B.cells.go(w, smap(t))), csum(~A, ~f, d, rt, B.cells.go(w, t)),
        csum_shift(~A, ~f, d, r, rt, w, t)) :
        {Nat.add(csum(~A, ~f, d, rt, B.row_cells(y, List.range(w))), _)
          == Nat.add(csum(~A, ~f, d, rt, B.row_cells(y, List.range(w))), csum(~A, ~f, d, rt, B.cells.go(w, t))) : Nat}
      {==}

law rsum_at_shift:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +a: A
  for +t: List<&2, A>
  for +xs: List<&2, Nat>
  {rsum_at(~A, ~f, d, a <> t, smap(xs)) == rsum_at(~A, ~f, d, t, xs) : Nat}

def rsum_at_shift(A, f, d, a, t, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> u:
      %Equal.sym(Nat, rsum_at(~A, ~f, d, a <> t, smap(u)), rsum_at(~A, ~f, d, t, u), rsum_at_shift(~A, ~f, d, a, t, u)) :
        {Nat.add(f(Maybe.default(&2, A, List.get(&2, A, t, x), d)), _)
          == Nat.add(f(Maybe.default(&2, A, List.get(&2, A, t, x), d)), rsum_at(~A, ~f, d, t, u)) : Nat}
      {==}

law rsum_at_full:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +r: List<&2, A>
  {rsum_at(~A, ~f, d, r, List.range(List.length(&2, A, r))) == rsum(~A, ~f, r) : Nat}

def rsum_at_full(A, f, d, r):
  match r:
    case Nil{}:
      {==}
    case a <> t:
      %Equal.sym(List<&2, Nat>, List.range(1n+List.length(&2, A, t)), 0n <> smap(List.range(List.length(&2, A, t))),
        range_cons(List.length(&2, A, t))) :
        {rsum_at(~A, ~f, d, a <> t, _) == Nat.add(f(a), rsum(~A, ~f, t)) : Nat}
      %Equal.sym(Nat, rsum_at(~A, ~f, d, a <> t, smap(List.range(List.length(&2, A, t)))),
        rsum_at(~A, ~f, d, t, List.range(List.length(&2, A, t))),
        rsum_at_shift(~A, ~f, d, a, t, List.range(List.length(&2, A, t)))) :
        {Nat.add(f(a), _) == Nat.add(f(a), rsum(~A, ~f, t)) : Nat}
      %Equal.sym(Nat, rsum_at(~A, ~f, d, t, List.range(List.length(&2, A, t))), rsum(~A, ~f, t), rsum_at_full(~A, ~f, d, t)) :
        {Nat.add(f(a), _) == Nat.add(f(a), rsum(~A, ~f, t)) : Nat}
      {==}

law gsum_cells_go:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +w: Nat
  for +g: T.Grid(A)
  for +wide: {B.rows_wide(A, w, g) == True{} : Bool}
  {csum(~A, ~f, d, g, B.cells.go(w, List.range(List.length(&2, List<&2, A>, g)))) == gsum(~A, ~f, g) : Nat}

def gsum_cells_go(A, f, d, w, g, wide):
  match g:
    case Nil{}:
      {==}
    case r <> rt:
      +g2 = {r <> rt : T.Grid(A)}
      +n = List.length(&2, List<&2, A>, rt)
      +lr = P.eq_sound(List.length(&2, A, r), w,
        P.and_true_l(Nat.is_eq(List.length(&2, A, r), w), B.rows_wide(A, w, rt), wide))
      %Equal.sym(List<&2, Nat>, List.range(1n+n), 0n <> smap(List.range(n)), range_cons(n)) :
        {csum(~A, ~f, d, g2, B.cells.go(w, _)) == Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, rt)) : Nat}
      %Equal.sym(Nat, csum(~A, ~f, d, g2, List.append(&2, T.Pos, B.row_cells(0n, List.range(w)), B.cells.go(w, smap(List.range(n))))),
        Nat.add(csum(~A, ~f, d, g2, B.row_cells(0n, List.range(w))), csum(~A, ~f, d, g2, B.cells.go(w, smap(List.range(n))))),
        csum_append(~A, ~f, d, g2, B.row_cells(0n, List.range(w)), B.cells.go(w, smap(List.range(n))))) :
        {_ == Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, rt)) : Nat}
      %Equal.sym(Nat, csum(~A, ~f, d, g2, B.row_cells(0n, List.range(w))), rsum_at(~A, ~f, d, r, List.range(w)),
        csum_row0(~A, ~f, d, r, rt, List.range(w))) :
        {Nat.add(_, csum(~A, ~f, d, g2, B.cells.go(w, smap(List.range(n))))) == Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, rt)) : Nat}
      %lr : {Nat.add(rsum_at(~A, ~f, d, r, List.range(_)), csum(~A, ~f, d, g2, B.cells.go(w, smap(List.range(n)))))
        == Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, rt)) : Nat}
      %Equal.sym(Nat, rsum_at(~A, ~f, d, r, List.range(List.length(&2, A, r))), rsum(~A, ~f, r), rsum_at_full(~A, ~f, d, r)) :
        {Nat.add(_, csum(~A, ~f, d, g2, B.cells.go(w, smap(List.range(n))))) == Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, rt)) : Nat}
      %Equal.sym(Nat, csum(~A, ~f, d, g2, B.cells.go(w, smap(List.range(n)))), csum(~A, ~f, d, rt, B.cells.go(w, List.range(n))),
        csum_shift(~A, ~f, d, r, rt, w, List.range(n))) :
        {Nat.add(rsum(~A, ~f, r), _) == Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, rt)) : Nat}
      %Equal.sym(Nat, csum(~A, ~f, d, rt, B.cells.go(w, List.range(n))), gsum(~A, ~f, rt),
        gsum_cells_go(~A, ~f, d, w, rt, P.and_true_r(Nat.is_eq(List.length(&2, A, r), w), B.rows_wide(A, w, rt), wide))) :
        {Nat.add(rsum(~A, ~f, r), _) == Nat.add(rsum(~A, ~f, r), gsum(~A, ~f, rt)) : Nat}
      {==}

# Summing over a w-by-h grid row by row equals summing over its cells.
law grid_sum:
  for ~A: Data
  for ~f: A -> Nat
  for +d: A
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for +sh: {B.shaped(A, w, h, g) == True{} : Bool}
  {csum(~A, ~f, d, g, B.cells(w, h)) == gsum(~A, ~f, g) : Nat}

def grid_sum(A, f, d, w, h, g, sh):
  %PL.shaped_len(A, w, h, g, sh) : {csum(~A, ~f, d, g, B.cells.go(w, List.range(_))) == gsum(~A, ~f, g) : Nat}
  gsum_cells_go(~A, ~f, d, w, g, PL.shaped_wide(A, w, h, g, sh))
