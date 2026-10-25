import Base
import ./types.bend as T
import ./board.bend as B
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG
import ./proof_copy.bend as PC
import ./proof_cells.bend as PS

# Lemmas about zero walks (LAWS.bend's zero_walk).

def and4(+a: Bool, +b: Bool, +c: Bool, +d: Bool) -> Bool:
  Bool.and(Bool.and(Bool.and(a, b), c), d)

law and4_d:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(Bool.and(a, b), c), d) == True{} : Bool}
  {d == True{} : Bool}

def and4_d(a, b, c, d, e):
  P.and_true_r(Bool.and(Bool.and(a, b), c), d, e)

law and4_c:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(Bool.and(a, b), c), d) == True{} : Bool}
  {c == True{} : Bool}

def and4_c(a, b, c, d, e):
  P.and_true_r(Bool.and(a, b), c, P.and_true_l(Bool.and(Bool.and(a, b), c), d, e))

law and4_b:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(Bool.and(a, b), c), d) == True{} : Bool}
  {b == True{} : Bool}

def and4_b(a, b, c, d, e):
  P.and_true_r(a, b, P.and_true_l(Bool.and(a, b), c, P.and_true_l(Bool.and(Bool.and(a, b), c), d, e)))

law and4_a:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for e: {Bool.and(Bool.and(Bool.and(a, b), c), d) == True{} : Bool}
  {a == True{} : Bool}

def and4_a(a, b, c, d, e):
  P.and_true_l(a, b, P.and_true_l(Bool.and(a, b), c, P.and_true_l(Bool.and(Bool.and(a, b), c), d, e)))

law and4_intro:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  for ec: {c == True{} : Bool}
  for ed: {d == True{} : Bool}
  {Bool.and(Bool.and(Bool.and(a, b), c), d) == True{} : Bool}

def and4_intro(a, b, c, d, ea, eb, ec, ed):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(Bool.and(Bool.and(_, b), c), d) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {Bool.and(Bool.and(Bool.and(True{}, _), c), d) == True{} : Bool}
  %Equal.sym(Bool, c, True{}, ec) : {Bool.and(Bool.and(True{}, _), d) == True{} : Bool}
  ed

law lsame_sound:
  for +p: T.Pos
  for +q: T.Pos
  for e: {L.same(p, q) == True{} : Bool}
  {p == q : T.Pos}

def lsame_sound(p, q, e):
  PG.same_sound(p, q, %Equal.sym(Bool, B.same(p, q), L.same(p, q), PC.same_eq(p, q)) :
    {_ == True{} : Bool}; e)

law lsame_refl:
  for +p: T.Pos
  {L.same(p, p) == True{} : Bool}

def lsame_refl(p):
  %PC.same_eq(p, p) : {_ == True{} : Bool}
  PG.same_refl(p)

# Extending a walk to c by one step from c (a zero) to r.
law walk_snoc:
  for +path: List<&2, T.Pos>
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  for +c: T.Pos
  for +r: T.Pos
  for +wk: {L.zero_walk(path, w, h, layout, p, c) == True{} : Bool}
  for +z: {L.zero(w, h, layout, c) == True{} : Bool}
  for +a: {L.adjacent(c, r) == True{} : Bool}
  for +on: {L.on_board(w, h, r) == True{} : Bool}
  {L.zero_walk(List.append(&2, T.Pos, path, [r]), w, h, layout, p, r) == True{} : Bool}

def walk_snoc(path, w, h, layout, p, c, r, wk, z, a, on):
  match path:
    case Nil{}:
      %Equal.sym(T.Pos, p, c, lsame_sound(p, c, wk)) :
        {Bool.and(Bool.and(Bool.and(L.zero(w, h, layout, _), L.adjacent(_, r)), L.on_board(w, h, r)),
          L.zero_walk(Nil{}, w, h, layout, r, r)) == True{} : Bool}
      and4_intro(L.zero(w, h, layout, c), L.adjacent(c, r), L.on_board(w, h, r), L.same(r, r),
        z, a, on, lsame_refl(r))
    case s <> t:
      +zp = L.zero(w, h, layout, p)
      +ps = L.adjacent(p, s)
      +os = L.on_board(w, h, s)
      +rest = L.zero_walk(t, w, h, layout, s, c)
      and4_intro(zp, ps, os, L.zero_walk(List.append(&2, T.Pos, t, [r]), w, h, layout, s, r),
        and4_a(zp, ps, os, rest, wk), and4_b(zp, ps, os, rest, wk), and4_c(zp, ps, os, rest, wk),
        walk_snoc(t, w, h, layout, s, c, r, and4_d(zp, ps, os, rest, wk), z, a, on))

law rev_acc:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, xs, acc) == List.append(&2, A, List.reverse.go(&2, A, xs, Nil{}), acc) : List<&2, A>}

def rev_acc(A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      +r = List.reverse.go(&2, A, t, Nil{})
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, t, [x]), List.append(&2, A, r, [x]), rev_acc(A, t, [x])) :
        {List.reverse.go(&2, A, t, x <> acc) == List.append(&2, A, _, acc) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, r, [x]), acc), List.append(&2, A, r, x <> acc),
        P.append_assoc(A, r, [x], acc)) :
        {List.reverse.go(&2, A, t, x <> acc) == _ : List<&2, A>}
      rev_acc(A, t, x <> acc)

law rev_cons:
  for -A: Data
  for +r: A
  for +back: List<&2, A>
  {List.reverse(&2, A, r <> back) == List.append(&2, A, List.reverse(&2, A, back), [r]) : List<&2, A>}

def rev_cons(A, r, back):
  rev_acc(A, back, [r])

# A walk ends on the board when it starts there.
law walk_on:
  for +path: List<&2, T.Pos>
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Pos
  for +q: T.Pos
  for +wk: {L.zero_walk(path, w, h, layout, s, q) == True{} : Bool}
  for +on: {L.on_board(w, h, s) == True{} : Bool}
  {L.on_board(w, h, q) == True{} : Bool}

def walk_on(path, w, h, layout, s, q, wk, on):
  match path:
    case Nil{}:
      %lsame_sound(s, q, wk) : {L.on_board(w, h, _) == True{} : Bool}
      on
    case r <> t:
      +zs = L.zero(w, h, layout, s)
      +sr = L.adjacent(s, r)
      +orr = L.on_board(w, h, r)
      +rest = L.zero_walk(t, w, h, layout, r, q)
      walk_on(t, w, h, layout, r, q, and4_d(zs, sr, orr, rest, wk), and4_c(zs, sr, orr, rest, wk))

# A walk from a safe cell only reaches safe cells.
law walk_safe:
  for +path: List<&2, T.Pos>
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Pos
  for +q: T.Pos
  for +wk: {L.zero_walk(path, w, h, layout, s, q) == True{} : Bool}
  for +safe: {L.mine(layout, s) == False{} : Bool}
  {L.mine(layout, q) == False{} : Bool}

def walk_safe(path, w, h, layout, s, q, wk, safe):
  match path:
    case Nil{}:
      %lsame_sound(s, q, wk) : {L.mine(layout, _) == False{} : Bool}
      safe
    case r <> t:
      +zs = L.zero(w, h, layout, s)
      +sr = L.adjacent(s, r)
      +orr = L.on_board(w, h, r)
      +rest = L.zero_walk(t, w, h, layout, r, q)
      +m = PS.neighbours_member(w, h, s, r,
        %Equal.sym(Bool, B.on_board(w, h, r), L.on_board(w, h, r), PC.on_board_eq(w, h, r)) :
          {_ == True{} : Bool}; and4_c(zs, sr, orr, rest, wk),
        %Equal.sym(Bool, B.adjacent(s, r), L.adjacent(s, r), PC.adjacent_eq(s, r)) :
          {_ == True{} : Bool}; and4_b(zs, sr, orr, rest, wk))
      +safe_r = PS.zero_nbr(w, h, layout, s, r,
        %Equal.sym(Bool, B.zero(w, h, layout, s), L.zero(w, h, layout, s), PC.zero_eq(w, h, layout, s)) :
          {_ == True{} : Bool}; and4_a(zs, sr, orr, rest, wk), m)
      walk_safe(t, w, h, layout, r, q, and4_d(zs, sr, orr, rest, wk),
        %PC.mine_eq(layout, r) : {_ == False{} : Bool}; safe_r)
