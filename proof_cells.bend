import Base
import ./types.bend as T
import ./board.bend as B
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG
import ./proof_copy.bend as PC

# Lemmas about lists of cells: membership, the board's cells, neighbours.

# Every cell of ps passes f (with e for f's context).
def allp(~E: Data, ~f: E -> T.Pos -> Bool, +e: E, ps: List<&2, T.Pos>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case q <> t:
      f(e, q) && allp(~E, ~f, e, t)

def allp_head(~E: Data, ~f: E -> T.Pos -> Bool, +e: E, +q: T.Pos, +t: List<&2, T.Pos>,
  h: {allp(~E, ~f, e, q <> t) == True{} : Bool}) -> {f(e, q) == True{} : Bool}:
  P.and_true_l(f(e, q), allp(~E, ~f, e, t), h)

def allp_tail(~E: Data, ~f: E -> T.Pos -> Bool, +e: E, +q: T.Pos, +t: List<&2, T.Pos>,
  h: {allp(~E, ~f, e, q <> t) == True{} : Bool}) -> {allp(~E, ~f, e, t) == True{} : Bool}:
  P.and_true_r(f(e, q), allp(~E, ~f, e, t), h)

def allp_member.go(~E: Data, ~f: E -> T.Pos -> Bool, +e: E, +p: T.Pos, +t: List<&2, T.Pos>, +q: T.Pos,
  +hd: {f(e, p) == True{} : Bool}, +b: Bool, be: {B.same(p, q) == b : Bool},
  m: {Bool.or(b, B.contains(t, q)) == True{} : Bool},
  ih: {B.contains(t, q) == True{} : Bool} -> {f(e, q) == True{} : Bool}) -> {f(e, q) == True{} : Bool}:
  match b:
    case True{}:
      %PG.same_sound(p, q, be) : {f(e, _) == True{} : Bool}
      hd
    case False{}:
      ih(m)

# A cell of a list whose cells all pass f passes f.
def allp_member(~E: Data, ~f: E -> T.Pos -> Bool, +e: E, ps: List<&2, T.Pos>, +q: T.Pos,
  +h: {allp(~E, ~f, e, ps) == True{} : Bool}, m: {B.contains(ps, q) == True{} : Bool}) ->
  {f(e, q) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({f(e, q) == True{} : Bool}, P.false_ne_true(m))
    case +p <> +t:
      allp_member.go(~E, ~f, e, p, t, q, allp_head(~E, ~f, e, p, t, h), B.same(p, q), {==}, m,
        mt => allp_member(~E, ~f, e, t, q, allp_tail(~E, ~f, e, p, t, h), mt))

# Membership
# ==========

def contains_append.or(+a: Bool, +b: Bool, +c: Bool) ->
  {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law contains_append:
  for +xs: List<&2, T.Pos>
  for +ys: List<&2, T.Pos>
  for +q: T.Pos
  {B.contains(List.append(&2, T.Pos, xs, ys), q) == Bool.or(B.contains(xs, q), B.contains(ys, q)) : Bool}

def contains_append(xs, ys, q):
  match xs:
    case Nil{}:
      {==}
    case p <> t:
      %Equal.sym(Bool, B.contains(List.append(&2, T.Pos, t, ys), q), Bool.or(B.contains(t, q), B.contains(ys, q)),
        contains_append(t, ys, q)) :
        {Bool.or(B.same(p, q), _) == Bool.or(Bool.or(B.same(p, q), B.contains(t, q)), B.contains(ys, q)) : Bool}
      contains_append.or(B.same(p, q), B.contains(t, q), B.contains(ys, q))

# A Nat list contains i.
def memn(xs: List<&2, Nat>, +i: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Nat.is_eq(x, i) || memn(t, i)

def or_true_r(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law memn_append_r:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for +i: Nat
  for e: {memn(ys, i) == True{} : Bool}
  {memn(List.append(&2, Nat, xs, ys), i) == True{} : Bool}

def memn_append_r(xs, ys, i, e):
  match xs:
    case Nil{}:
      e
    case x <> t:
      %Equal.sym(Bool, memn(List.append(&2, Nat, t, ys), i), True{}, memn_append_r(t, ys, i, e)) :
        {Bool.or(Nat.is_eq(x, i), _) == True{} : Bool}
      or_true_r(Nat.is_eq(x, i))

law memn_append_l:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for +i: Nat
  for e: {memn(xs, i) == True{} : Bool}
  {memn(List.append(&2, Nat, xs, ys), i) == True{} : Bool}

def memn_append_l.go(+x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, +i: Nat, +b: Bool,
  e: {Bool.or(b, memn(t, i)) == True{} : Bool},
  ih: {memn(t, i) == True{} : Bool} -> {memn(List.append(&2, Nat, t, ys), i) == True{} : Bool}) ->
  {Bool.or(b, memn(List.append(&2, Nat, t, ys), i)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(e)

def memn_append_l(xs, ys, i, e):
  match xs:
    case Nil{}:
      Empty.absurd({memn(ys, i) == True{} : Bool}, P.false_ne_true(e))
    case x <> t:
      memn_append_l.go(x, t, ys, i, Nat.is_eq(x, i), e, et => memn_append_l(t, ys, i, et))

def memn_range.cases(+p: Nat, +i: Nat, r: Or({Nat.is_lt(i, p) == True{} : Bool}, {i == p : Nat}),
  ih: {Nat.is_lt(i, p) == True{} : Bool} -> {memn(List.range(p), i) == True{} : Bool}) ->
  {memn(List.append(&2, Nat, List.range(p), [p]), i) == True{} : Bool}:
  match r:
    case Inl{lt}:
      memn_append_l(List.range(p), [p], i, ih(lt))
    case Inr{eq}:
      memn_append_r(List.range(p), [p], i,
        %Equal.sym(Nat, i, p, eq) : {Bool.or(Nat.is_eq(p, _), False{}) == True{} : Bool};
        %Equal.sym(Bool, Nat.is_eq(p, p), True{}, P.eq_refl(p)) : {Bool.or(_, False{}) == True{} : Bool};
        {==})

law memn_range:
  for +n: Nat
  for +i: Nat
  for e: {Nat.is_lt(i, n) == True{} : Bool}
  {memn(List.range(n), i) == True{} : Bool}

def memn_range(n, i, e):
  match n:
    case 0n:
      Empty.absurd({memn(List.range(0n), i) == True{} : Bool},
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)), e)))
    case 1n+p:
      %Equal.sym(List<&2, Nat>, List.range(1n+p), List.append(&2, Nat, List.range(p), [p]), P.range_snoc(p)) :
        {memn(_, i) == True{} : Bool}
      memn_range.cases(p, i, P.lt_succ(i, p, e), lt => memn_range(p, i, lt))

def contains_row.go(+y: Nat, +a: Nat, +t: List<&2, Nat>, +x: Nat, +b: Bool,
  e: {Bool.or(b, memn(t, x)) == True{} : Bool}, be: {Nat.is_eq(a, x) == b : Bool},
  ih: {memn(t, x) == True{} : Bool} -> {B.contains(B.row_cells(y, t), T.Pos{x, y}) == True{} : Bool}) ->
  {Bool.or(B.same(T.Pos{a, y}, T.Pos{x, y}), B.contains(B.row_cells(y, t), T.Pos{x, y})) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(a, x), True{}, be) :
        {Bool.or(Bool.and(_, Nat.is_eq(y, y)), B.contains(B.row_cells(y, t), T.Pos{x, y})) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(y, y), True{}, P.eq_refl(y)) :
        {Bool.or(Bool.and(True{}, _), B.contains(B.row_cells(y, t), T.Pos{x, y})) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, B.contains(B.row_cells(y, t), T.Pos{x, y}), True{}, ih(e)) :
        {Bool.or(B.same(T.Pos{a, y}, T.Pos{x, y}), _) == True{} : Bool}
      or_true_r(B.same(T.Pos{a, y}, T.Pos{x, y}))

law contains_row:
  for +y: Nat
  for +xs: List<&2, Nat>
  for +x: Nat
  for e: {memn(xs, x) == True{} : Bool}
  {B.contains(B.row_cells(y, xs), T.Pos{x, y}) == True{} : Bool}

def contains_row(y, xs, x, e):
  match xs:
    case Nil{}:
      Empty.absurd({B.contains(Nil{}, T.Pos{x, y}) == True{} : Bool}, P.false_ne_true(e))
    case a <> t:
      contains_row.go(y, a, t, x, Nat.is_eq(a, x), e, {==}, et => contains_row(y, t, x, et))

def contains_cells.k(+w: Nat, +a: Nat, +t: List<&2, Nat>, +x: Nat, +y: Nat,
  xm: {memn(List.range(w), x) == True{} : Bool}, +b: Bool,
  e: {Bool.or(b, memn(t, y)) == True{} : Bool}, be: {Nat.is_eq(a, y) == b : Bool},
  ih: {memn(t, y) == True{} : Bool} -> {B.contains(B.cells.go(w, t), T.Pos{x, y}) == True{} : Bool}) ->
  {Bool.or(B.contains(B.row_cells(a, List.range(w)), T.Pos{x, y}), B.contains(B.cells.go(w, t), T.Pos{x, y}))
    == True{} : Bool}:
  match b:
    case True{}:
      %P.eq_sound(a, y, be) :
        {Bool.or(B.contains(B.row_cells(a, List.range(w)), T.Pos{x, _}), B.contains(B.cells.go(w, t), T.Pos{x, y}))
          == True{} : Bool}
      %Equal.sym(Bool, B.contains(B.row_cells(a, List.range(w)), T.Pos{x, a}), True{},
        contains_row(a, List.range(w), x, xm)) :
        {Bool.or(_, B.contains(B.cells.go(w, t), T.Pos{x, y})) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, B.contains(B.cells.go(w, t), T.Pos{x, y}), True{}, ih(e)) :
        {Bool.or(B.contains(B.row_cells(a, List.range(w)), T.Pos{x, y}), _) == True{} : Bool}
      or_true_r(B.contains(B.row_cells(a, List.range(w)), T.Pos{x, y}))

def contains_cells.go(+w: Nat, +a: Nat, +t: List<&2, Nat>, +x: Nat, +y: Nat,
  xm: {memn(List.range(w), x) == True{} : Bool}, +b: Bool,
  e: {Bool.or(b, memn(t, y)) == True{} : Bool}, be: {Nat.is_eq(a, y) == b : Bool},
  ih: {memn(t, y) == True{} : Bool} -> {B.contains(B.cells.go(w, t), T.Pos{x, y}) == True{} : Bool}) ->
  {B.contains(List.append(&2, T.Pos, B.row_cells(a, List.range(w)), B.cells.go(w, t)), T.Pos{x, y}) == True{} : Bool}:
  +row = B.row_cells(a, List.range(w))
  %Equal.sym(Bool, B.contains(List.append(&2, T.Pos, row, B.cells.go(w, t)), T.Pos{x, y}),
    Bool.or(B.contains(row, T.Pos{x, y}), B.contains(B.cells.go(w, t), T.Pos{x, y})),
    contains_append(row, B.cells.go(w, t), T.Pos{x, y})) : {_ == True{} : Bool}
  contains_cells.k(w, a, t, x, y, xm, b, e, be, ih)

law contains_cells:
  for +w: Nat
  for +ys: List<&2, Nat>
  for +x: Nat
  for +y: Nat
  for +xm: {memn(List.range(w), x) == True{} : Bool}
  for e: {memn(ys, y) == True{} : Bool}
  {B.contains(B.cells.go(w, ys), T.Pos{x, y}) == True{} : Bool}

def contains_cells(w, ys, x, y, xm, e):
  match ys:
    case Nil{}:
      Empty.absurd({B.contains(Nil{}, T.Pos{x, y}) == True{} : Bool}, P.false_ne_true(e))
    case a <> t:
      contains_cells.go(w, a, t, x, y, xm, Nat.is_eq(a, y), e, {==}, et => contains_cells(w, t, x, y, xm, et))

# Every cell of the board is one of its cells.
law cells_member:
  for +w: Nat
  for +h: Nat
  for +q: T.Pos
  for +on: {B.on_board(w, h, q) == True{} : Bool}
  {B.contains(B.cells(w, h), q) == True{} : Bool}

def cells_member(w, h, q, on):
  match q:
    case T.Pos{x, y}:
      contains_cells(w, List.range(h), x, y,
        memn_range(w, x, P.and_true_l(Nat.is_lt(x, w), Nat.is_lt(y, h), on)),
        memn_range(h, y, P.and_true_r(Nat.is_lt(x, w), Nat.is_lt(y, h), on)))

# The board's cells are on the board
# ==================================

type WH is Data:
  WH{w: Nat, h: Nat}

def onb(e: WH, q: T.Pos) -> Bool:
  match e:
    case WH{w, h}:
      B.on_board(w, h, q)

law allp_append:
  for ~E: Data
  for ~f: E -> T.Pos -> Bool
  for +e: E
  for +xs: List<&2, T.Pos>
  for +ys: List<&2, T.Pos>
  for +a: {allp(~E, ~f, e, xs) == True{} : Bool}
  for b: {allp(~E, ~f, e, ys) == True{} : Bool}
  {allp(~E, ~f, e, List.append(&2, T.Pos, xs, ys)) == True{} : Bool}

def allp_append(E, f, e, xs, ys, a, b):
  match xs:
    case Nil{}:
      b
    case q <> t:
      %Equal.sym(Bool, allp(~E, ~f, e, List.append(&2, T.Pos, t, ys)), True{},
        allp_append(~E, ~f, e, t, ys, allp_tail(~E, ~f, e, q, t, a), b)) :
        {Bool.and(f(e, q), _) == True{} : Bool}
      %Equal.sym(Bool, f(e, q), True{}, allp_head(~E, ~f, e, q, t, a)) :
        {Bool.and(_, True{}) == True{} : Bool}
      {==}

# Every element of xs is below n.
def alln(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_lt(x, n) && alln(t, n)

law lt_mono:
  for +i: Nat
  for +n: Nat
  for e: {Nat.is_lt(i, n) == True{} : Bool}
  {Nat.is_lt(i, 1n+n) == True{} : Bool}

def lt_mono(i, n, e):
  match i n:
    case 0n _:
      {==}
    case 1n+j 0n:
      Empty.absurd({Nat.is_lt(1n+j, 1n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+j 1n+m:
      lt_mono(j, m, e)

law lt_succ_self:
  for +n: Nat
  {Nat.is_lt(n, 1n+n) == True{} : Bool}

def lt_succ_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ_self(p)

law alln_mono:
  for +xs: List<&2, Nat>
  for +n: Nat
  for +e: {alln(xs, n) == True{} : Bool}
  {alln(xs, 1n+n) == True{} : Bool}

def alln_mono(xs, n, e):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Bool, Nat.is_lt(x, 1n+n), True{},
        lt_mono(x, n, P.and_true_l(Nat.is_lt(x, n), alln(t, n), e))) :
        {Bool.and(_, alln(t, 1n+n)) == True{} : Bool}
      alln_mono(t, n, P.and_true_r(Nat.is_lt(x, n), alln(t, n), e))

law alln_append:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for +n: Nat
  for +a: {alln(xs, n) == True{} : Bool}
  for b: {alln(ys, n) == True{} : Bool}
  {alln(List.append(&2, Nat, xs, ys), n) == True{} : Bool}

def alln_append(xs, ys, n, a, b):
  match xs:
    case Nil{}:
      b
    case x <> t:
      %Equal.sym(Bool, Nat.is_lt(x, n), True{}, P.and_true_l(Nat.is_lt(x, n), alln(t, n), a)) :
        {Bool.and(_, alln(List.append(&2, Nat, t, ys), n)) == True{} : Bool}
      alln_append(t, ys, n, P.and_true_r(Nat.is_lt(x, n), alln(t, n), a), b)

law alln_range:
  for +n: Nat
  {alln(List.range(n), n) == True{} : Bool}

def alln_range(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Nat>, List.range(1n+p), List.append(&2, Nat, List.range(p), [p]), P.range_snoc(p)) :
        {alln(_, 1n+p) == True{} : Bool}
      alln_append(List.range(p), [p], 1n+p, alln_mono(List.range(p), p, alln_range(p)),
        %Equal.sym(Bool, Nat.is_lt(p, 1n+p), True{}, lt_succ_self(p)) :
          {Bool.and(_, True{}) == True{} : Bool}; {==})

law row_on:
  for +w: Nat
  for +h: Nat
  for +y: Nat
  for +xs: List<&2, Nat>
  for +yh: {Nat.is_lt(y, h) == True{} : Bool}
  for +xw: {alln(xs, w) == True{} : Bool}
  {allp(~WH, ~onb, WH{w, h}, B.row_cells(y, xs)) == True{} : Bool}

def row_on(w, h, y, xs, yh, xw):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Bool, Nat.is_lt(x, w), True{}, P.and_true_l(Nat.is_lt(x, w), alln(t, w), xw)) :
        {Bool.and(Bool.and(_, Nat.is_lt(y, h)), allp(~WH, ~onb, WH{w, h}, B.row_cells(y, t))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_lt(y, h), True{}, yh) :
        {Bool.and(Bool.and(True{}, _), allp(~WH, ~onb, WH{w, h}, B.row_cells(y, t))) == True{} : Bool}
      row_on(w, h, y, t, yh, P.and_true_r(Nat.is_lt(x, w), alln(t, w), xw))

law cells_on.go:
  for +w: Nat
  for +h: Nat
  for +ys: List<&2, Nat>
  for +yh: {alln(ys, h) == True{} : Bool}
  {allp(~WH, ~onb, WH{w, h}, B.cells.go(w, ys)) == True{} : Bool}

def cells_on.go(w, h, ys, yh):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      allp_append(~WH, ~onb, WH{w, h}, B.row_cells(y, List.range(w)), B.cells.go(w, t),
        row_on(w, h, y, List.range(w), P.and_true_l(Nat.is_lt(y, h), alln(t, h), yh), alln_range(w)),
        cells_on.go(w, h, t, P.and_true_r(Nat.is_lt(y, h), alln(t, h), yh)))

# Every cell of cells(w, h) is on the board.
law cells_on:
  for +w: Nat
  for +h: Nat
  {allp(~WH, ~onb, WH{w, h}, B.cells(w, h)) == True{} : Bool}

def cells_on(w, h):
  cells_on.go(w, h, List.range(h), alln_range(h))

# Neighbours
# ==========

law put_keeps:
  for +e0: T.Pos
  for +xs: List<&2, T.Pos>
  for +c: Bool
  for +r: T.Pos
  for m: {B.contains(xs, r) == True{} : Bool}
  {B.contains(List.filter.put(T.Pos, e0, xs, c), r) == True{} : Bool}

def put_keeps(e0, xs, c, r, m):
  match c:
    case True{}:
      %Equal.sym(Bool, B.contains(xs, r), True{}, m) : {Bool.or(B.same(e0, r), _) == True{} : Bool}
      or_true_r(B.same(e0, r))
    case False{}:
      m

def touching_member.go(+s: T.Pos, +e0: T.Pos, +t: List<&2, T.Pos>, +r: T.Pos,
  a: {B.adjacent(s, r) == True{} : Bool}, +b: Bool, be: {B.same(e0, r) == b : Bool},
  m: {Bool.or(b, B.contains(t, r)) == True{} : Bool},
  ih: {B.contains(t, r) == True{} : Bool} -> {B.contains(B.touching(s, t), r) == True{} : Bool}) ->
  {B.contains(List.filter.put(T.Pos, e0, B.touching(s, t), B.adjacent(s, e0)), r) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(T.Pos, e0, r, PG.same_sound(e0, r, be)) :
        {B.contains(List.filter.put(T.Pos, _, B.touching(s, t), B.adjacent(s, _)), r) == True{} : Bool}
      %Equal.sym(Bool, B.adjacent(s, r), True{}, a) :
        {B.contains(List.filter.put(T.Pos, r, B.touching(s, t), _), r) == True{} : Bool}
      PG.contains_cons_self(r, B.touching(s, t))
    case False{}:
      put_keeps(e0, B.touching(s, t), B.adjacent(s, e0), r, ih(m))

law touching_member:
  for +s: T.Pos
  for +xs: List<&2, T.Pos>
  for +r: T.Pos
  for +a: {B.adjacent(s, r) == True{} : Bool}
  for m: {B.contains(xs, r) == True{} : Bool}
  {B.contains(B.touching(s, xs), r) == True{} : Bool}

def touching_member(s, xs, r, a, m):
  match xs:
    case Nil{}:
      Empty.absurd({B.contains(Nil{}, r) == True{} : Bool}, P.false_ne_true(m))
    case e0 <> t:
      touching_member.go(s, e0, t, r, a, B.same(e0, r), {==}, m, mt => touching_member(s, t, r, a, mt))

# An adjacent cell of the board is a neighbour.
law neighbours_member:
  for +w: Nat
  for +h: Nat
  for +s: T.Pos
  for +r: T.Pos
  for on: {B.on_board(w, h, r) == True{} : Bool}
  for a: {B.adjacent(s, r) == True{} : Bool}
  {B.contains(B.neighbours(w, h, s), r) == True{} : Bool}

def neighbours_member(w, h, s, r, on, a):
  touching_member(s, B.cells(w, h), r, a, cells_member(w, h, r, on))

type WHS is Data:
  WHS{w: Nat, h: Nat, s: T.Pos}

def adj_on.go(e: WHS, +q: T.Pos) -> Bool:
  match e:
    case WHS{w, h, s}:
      B.adjacent(s, q) && B.on_board(w, h, q)

def adj_on(e: WHS, q: T.Pos) -> Bool:
  adj_on.go(e, q)

def touching_all.go(+w: Nat, +h: Nat, +s: T.Pos, +q: T.Pos, +t: List<&2, T.Pos>,
  qon: {B.on_board(w, h, q) == True{} : Bool}, +c: Bool, ce: {B.adjacent(s, q) == c : Bool},
  ih: {allp(~WHS, ~adj_on, WHS{w, h, s}, B.touching(s, t)) == True{} : Bool}) ->
  {allp(~WHS, ~adj_on, WHS{w, h, s}, List.filter.put(T.Pos, q, B.touching(s, t), c)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, B.adjacent(s, q), True{}, ce) :
        {Bool.and(Bool.and(_, B.on_board(w, h, q)), allp(~WHS, ~adj_on, WHS{w, h, s}, B.touching(s, t))) == True{} : Bool}
      %Equal.sym(Bool, B.on_board(w, h, q), True{}, qon) :
        {Bool.and(Bool.and(True{}, _), allp(~WHS, ~adj_on, WHS{w, h, s}, B.touching(s, t))) == True{} : Bool}
      ih
    case False{}:
      ih

law touching_all:
  for +w: Nat
  for +h: Nat
  for +s: T.Pos
  for +xs: List<&2, T.Pos>
  for +on: {allp(~WH, ~onb, WH{w, h}, xs) == True{} : Bool}
  {allp(~WHS, ~adj_on, WHS{w, h, s}, B.touching(s, xs)) == True{} : Bool}

def touching_all(w, h, s, xs, on):
  match xs:
    case Nil{}:
      {==}
    case q <> t:
      touching_all.go(w, h, s, q, t, allp_head(~WH, ~onb, WH{w, h}, q, t, on), B.adjacent(s, q), {==},
        touching_all(w, h, s, t, allp_tail(~WH, ~onb, WH{w, h}, q, t, on)))

# Every neighbour of s is adjacent to s and on the board.
law neighbours_all:
  for +w: Nat
  for +h: Nat
  for +s: T.Pos
  {allp(~WHS, ~adj_on, WHS{w, h, s}, B.neighbours(w, h, s)) == True{} : Bool}

def neighbours_all(w, h, s):
  touching_all(w, h, s, B.cells(w, h), cells_on(w, h))

# Zeros
# =====

law add_zero_l:
  for +a: Nat
  for +b: Nat
  for e: {Nat.add(a, b) == 0n : Nat}
  {a == 0n : Nat}

def add_zero_l(a, b, e):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, P.succ_ne_zero(Nat.add(p, b), e))

law add_zero_r:
  for +a: Nat
  for +b: Nat
  for e: {Nat.add(a, b) == 0n : Nat}
  {b == 0n : Nat}

def add_zero_r(a, b, e):
  match a:
    case 0n:
      e
    case 1n+p:
      Empty.absurd({b == 0n : Nat}, P.succ_ne_zero(Nat.add(p, b), e))

law one_zero:
  for +b: Bool
  for e: {Bool.pick(Nat, b, 1n, 0n) == 0n : Nat}
  {b == False{} : Bool}

def one_zero(b, e):
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.succ_ne_zero(0n, e))

def count_zero_member.go(+layout: T.Grid(Bool), +q: T.Pos, +t: List<&2, T.Pos>, +r: T.Pos,
  mq: {B.mine(layout, q) == False{} : Bool}, +b: Bool, be: {B.same(q, r) == b : Bool},
  m: {Bool.or(b, B.contains(t, r)) == True{} : Bool},
  ih: {B.contains(t, r) == True{} : Bool} -> {B.mine(layout, r) == False{} : Bool}) ->
  {B.mine(layout, r) == False{} : Bool}:
  match b:
    case True{}:
      %PG.same_sound(q, r, be) : {B.mine(layout, _) == False{} : Bool}
      mq
    case False{}:
      ih(m)

# A list with no mines has no mine on any of its cells.
law count_zero_member:
  for +layout: T.Grid(Bool)
  for +ns: List<&2, T.Pos>
  for +r: T.Pos
  for +z: {B.count_mines(layout, ns) == 0n : Nat}
  for m: {B.contains(ns, r) == True{} : Bool}
  {B.mine(layout, r) == False{} : Bool}

def count_zero_member(layout, ns, r, z, m):
  match ns:
    case Nil{}:
      Empty.absurd({B.mine(layout, r) == False{} : Bool}, P.false_ne_true(m))
    case q <> t:
      +c = B.count_mines(layout, t)
      count_zero_member.go(layout, q, t, r,
        one_zero(B.mine(layout, q), add_zero_l(Bool.pick(Nat, B.mine(layout, q), 1n, 0n), c, z)),
        B.same(q, r), {==}, m,
        mt => count_zero_member(layout, t, r, add_zero_r(Bool.pick(Nat, B.mine(layout, q), 1n, 0n), c, z), mt))

# The neighbours of a zero have no mines.
law zero_nbr:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Pos
  for +r: T.Pos
  for z: {B.zero(w, h, layout, s) == True{} : Bool}
  for m: {B.contains(B.neighbours(w, h, s), r) == True{} : Bool}
  {B.mine(layout, r) == False{} : Bool}

def zero_nbr(w, h, layout, s, r, z, m):
  +a = Bool.and(B.on_board(w, h, s), Bool.not(B.mine(layout, s)))
  +adj = B.adj_mines(w, h, layout, s)
  count_zero_member(layout, B.neighbours(w, h, s), r,
    P.eq_sound(adj, 0n, P.and_true_r(a, Nat.is_eq(adj, 0n), z)), m)
