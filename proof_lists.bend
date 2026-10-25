import Base
import ./types.bend as T
import ./board.bend as B
import ./proof_base.bend as P

# Lemmas about updating lists and grids.

def Maybe.disc_n(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def none_ne_some(-A: Data, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %e : Maybe.disc_n(A, _)
  Unit{}

def Maybe.val(-A: Data, +d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def some_inj(-A: Data, +a: A, +x: A, e: {Some{a} == Some{x} : Maybe<&2, A>}) -> {a == x : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.val(A, a, m), Some{a}, Some{x}, e)

# List.set
# ========

law set_len:
  for -A: Data
  for +xs: List<&2, A>
  for +i: Nat
  for +v: A
  {List.length(&2, A, List.set(&2, A, xs, i, v)) == List.length(&2, A, xs) : Nat}

def set_len(A, xs, i, v):
  match xs i:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      %Equal.sym(Nat, List.length(&2, A, List.set(&2, A, t, k, v)), List.length(&2, A, t), set_len(A, t, k, v)) :
        {1n+_ == 1n+List.length(&2, A, t) : Nat}
      {==}

law get_set_eq:
  for -A: Data
  for +xs: List<&2, A>
  for +i: Nat
  for +v: A
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {List.get(&2, A, List.set(&2, A, xs, i, v), i) == Some{v} : Maybe<&2, A>}

def get_set_eq(A, xs, i, v, e):
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, A, List.set(&2, A, Nil{}, i, v), i) == Some{v} : Maybe<&2, A>},
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)), e)))
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      get_set_eq(A, t, k, v, e)

law get_set_ne:
  for -A: Data
  for +xs: List<&2, A>
  for +i: Nat
  for +j: Nat
  for +v: A
  for e: {Nat.is_eq(i, j) == False{} : Bool}
  {List.get(&2, A, List.set(&2, A, xs, i, v), j) == List.get(&2, A, xs, j) : Maybe<&2, A>}

def get_set_ne(A, xs, i, j, v, e):
  match xs i j:
    case Nil{} _ _:
      {==}
    case h <> t 0n 0n:
      Empty.absurd({List.get(&2, A, v <> t, 0n) == List.get(&2, A, h <> t, 0n) : Maybe<&2, A>},
        P.true_ne_false(e))
    case h <> t 0n 1n+q:
      {==}
    case h <> t 1n+k 0n:
      {==}
    case h <> t 1n+k 1n+q:
      get_set_ne(A, t, k, q, v, e)

# Setting an index past the end changes nothing.
law set_out:
  for -A: Data
  for +xs: List<&2, A>
  for +i: Nat
  for +v: A
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == False{} : Bool}
  {List.set(&2, A, xs, i, v) == xs : List<&2, A>}

def set_out(A, xs, i, v, e):
  match xs i:
    case Nil{} _:
      {==}
    case h <> t 0n:
      Empty.absurd({List.set(&2, A, h <> t, 0n, v) == h <> t : List<&2, A>}, P.true_ne_false(e))
    case h <> t 1n+k:
      %Equal.sym(List<&2, A>, List.set(&2, A, t, k, v), t, set_out(A, t, k, v, e)) :
        {h <> _ == h <> t : List<&2, A>}
      {==}

# Inside a list, an index reads Some of its default.
law get_in:
  for -A: Data
  for +xs: List<&2, A>
  for +i: Nat
  for +d: A
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {List.get(&2, A, xs, i) == Some{Maybe.default(&2, A, List.get(&2, A, xs, i), d)} : Maybe<&2, A>}

def get_in(A, xs, i, d, e):
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, A, Nil{}, i) == Some{Maybe.default(&2, A, List.get(&2, A, Nil{}, i), d)}
        : Maybe<&2, A>},
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)), e)))
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      get_in(A, t, k, d, e)

# A row of a grid whose rows all have w cells has w cells.
law rows_wide_get:
  for -A: Data
  for +w: Nat
  for +g: T.Grid(A)
  for +i: Nat
  for +r: List<&2, A>
  for wide: {B.rows_wide(A, w, g) == True{} : Bool}
  for e: {List.get(&2, List<&2, A>, g, i) == Some{r} : Maybe<&2, List<&2, A>>}
  {List.length(&2, A, r) == w : Nat}

def rows_wide_get(A, w, g, i, r, wide, e):
  match g i:
    case Nil{} _:
      Empty.absurd({List.length(&2, A, r) == w : Nat}, none_ne_some(List<&2, A>, r, e))
    case row <> t 0n:
      %some_inj(List<&2, A>, row, r, e) : {List.length(&2, A, _) == w : Nat}
      P.eq_sound(List.length(&2, A, row), w,
        P.and_true_l(Nat.is_eq(List.length(&2, A, row), w), B.rows_wide(A, w, t), wide))
    case row <> t 1n+k:
      rows_wide_get(A, w, t, k, r,
        P.and_true_r(Nat.is_eq(List.length(&2, A, row), w), B.rows_wide(A, w, t), wide), e)


# Grids
# =====

def row_of(-A: Data, +g: T.Grid(A), +y: Nat) -> List<&2, A>:
  Maybe.default(&2, List<&2, A>, List.get(&2, List<&2, A>, g, y), Nil{})

law shaped_len:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for sh: {B.shaped(A, w, h, g) == True{} : Bool}
  {List.length(&2, List<&2, A>, g) == h : Nat}

def shaped_len(A, w, h, g, sh):
  P.eq_sound(List.length(&2, List<&2, A>, g), h,
    P.and_true_l(Nat.is_eq(List.length(&2, List<&2, A>, g), h), B.rows_wide(A, w, g), sh))

law shaped_wide:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for sh: {B.shaped(A, w, h, g) == True{} : Bool}
  {B.rows_wide(A, w, g) == True{} : Bool}

def shaped_wide(A, w, h, g, sh):
  P.and_true_r(Nat.is_eq(List.length(&2, List<&2, A>, g), h), B.rows_wide(A, w, g), sh)

# In a w-by-h grid, the row at y < h is its row and has w cells.
law row_in:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for +y: Nat
  for +sh: {B.shaped(A, w, h, g) == True{} : Bool}
  for yh: {Nat.is_lt(y, h) == True{} : Bool}
  {List.get(&2, List<&2, A>, g, y) == Some{row_of(A, g, y)} : Maybe<&2, List<&2, A>>} &
  {List.length(&2, A, row_of(A, g, y)) == w : Nat}

def row_in(A, w, h, g, y, sh, yh):
  +yl = {%Equal.sym(Nat, List.length(&2, List<&2, A>, g), h, shaped_len(A, w, h, g, sh)) :
    {Nat.is_lt(y, _) == True{} : Bool};
    yh : {Nat.is_lt(y, List.length(&2, List<&2, A>, g)) == True{} : Bool}}
  +gi = get_in(List<&2, A>, g, y, Nil{}, yl)
  (gi, rows_wide_get(A, w, g, y, row_of(A, g, y), shaped_wide(A, w, h, g, sh), gi))

law at_set_eq:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for +x: Nat
  for +y: Nat
  for +v: A
  for +d: A
  for +sh: {B.shaped(A, w, h, g) == True{} : Bool}
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  {B.at(A, d, B.set_at(A, g, T.Pos{x, y}, v), T.Pos{x, y}) == v : A}

law row_in_get:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for +y: Nat
  for +sh: {B.shaped(A, w, h, g) == True{} : Bool}
  for yh: {Nat.is_lt(y, h) == True{} : Bool}
  {List.get(&2, List<&2, A>, g, y) == Some{row_of(A, g, y)} : Maybe<&2, List<&2, A>>}

def row_in_get(A, w, h, g, y, sh, yh):
  get_in(List<&2, A>, g, y, Nil{},
    {%Equal.sym(Nat, List.length(&2, List<&2, A>, g), h, shaped_len(A, w, h, g, sh)) :
      {Nat.is_lt(y, _) == True{} : Bool};
      yh : {Nat.is_lt(y, List.length(&2, List<&2, A>, g)) == True{} : Bool}})

law row_in_len:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for +y: Nat
  for +sh: {B.shaped(A, w, h, g) == True{} : Bool}
  for yh: {Nat.is_lt(y, h) == True{} : Bool}
  {List.length(&2, A, row_of(A, g, y)) == w : Nat}

def row_in_len(A, w, h, g, y, sh, yh):
  rows_wide_get(A, w, g, y, row_of(A, g, y), shaped_wide(A, w, h, g, sh), row_in_get(A, w, h, g, y, sh, yh))

def at_set_eq(A, w, h, g, x, y, v, d, sh, on):
  +xw = P.and_true_l(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +yh = P.and_true_r(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  ri = row_in(A, w, h, g, y, sh, yh)
  +row = row_of(A, g, y)
  +yl = {%Equal.sym(Nat, List.length(&2, List<&2, A>, g), h, shaped_len(A, w, h, g, sh)) :
    {Nat.is_lt(y, _) == True{} : Bool};
    yh : {Nat.is_lt(y, List.length(&2, List<&2, A>, g)) == True{} : Bool}}
  +xl = {%Equal.sym(Nat, List.length(&2, A, row), w,
      Pair.snd({List.get(&2, List<&2, A>, g, y) == Some{row} : Maybe<&2, List<&2, A>>},
      {List.length(&2, A, row) == w : Nat}, ri)) : {Nat.is_lt(x, _) == True{} : Bool};
    xw : {Nat.is_lt(x, List.length(&2, A, row)) == True{} : Bool}}
  +r2 = List.set(&2, A, row, x, v)
  %Equal.sym(Maybe<&2, List<&2, A>>, List.get(&2, List<&2, A>, List.set(&2, List<&2, A>, g, y, r2), y),
    Some{r2}, get_set_eq(List<&2, A>, g, y, r2, yl)) :
    {Maybe.default(&2, A, List.get(&2, A, Maybe.default(&2, List<&2, A>, _, Nil{}), x), d) == v : A}
  %Equal.sym(Maybe<&2, A>, List.get(&2, A, r2, x), Some{v}, get_set_eq(A, row, x, v, xl)) :
    {Maybe.default(&2, A, _, d) == v : A}
  {==}

def at_set_ne.row(-A: Data, +g: T.Grid(A), +x: Nat, +y: Nat, +qx: Nat, +v: A, +d: A,
  xne: {Nat.is_eq(x, qx) == False{} : Bool}, +c: Bool,
  ce: {Nat.is_lt(y, List.length(&2, List<&2, A>, g)) == c : Bool}) ->
  {B.at(A, d, B.set_at(A, g, T.Pos{x, y}, v), T.Pos{qx, y}) == B.at(A, d, g, T.Pos{qx, y}) : A}:
  match c:
    case True{}:
      +row = row_of(A, g, y)
      +r2 = List.set(&2, A, row, x, v)
      %Equal.sym(Maybe<&2, List<&2, A>>, List.get(&2, List<&2, A>, List.set(&2, List<&2, A>, g, y, r2), y),
        Some{r2}, get_set_eq(List<&2, A>, g, y, r2, ce)) :
        {Maybe.default(&2, A, List.get(&2, A, Maybe.default(&2, List<&2, A>, _, Nil{}), qx), d)
          == B.at(A, d, g, T.Pos{qx, y}) : A}
      %Equal.sym(Maybe<&2, A>, List.get(&2, A, r2, qx), List.get(&2, A, row, qx),
        get_set_ne(A, row, x, qx, v, xne)) :
        {Maybe.default(&2, A, _, d) == B.at(A, d, g, T.Pos{qx, y}) : A}
      {==}
    case False{}:
      +r2 = List.set(&2, A, row_of(A, g, y), x, v)
      %Equal.sym(T.Grid(A), List.set(&2, List<&2, A>, g, y, r2), g, set_out(List<&2, A>, g, y, r2, ce)) :
        {B.at(A, d, _, T.Pos{qx, y}) == B.at(A, d, g, T.Pos{qx, y}) : A}
      {==}

def at_set_ne.go(-A: Data, +g: T.Grid(A), +x: Nat, +y: Nat, +qx: Nat, +qy: Nat, +v: A, +d: A,
  ne: {B.same(T.Pos{x, y}, T.Pos{qx, qy}) == False{} : Bool}, +b: Bool,
  +be: {Nat.is_eq(y, qy) == b : Bool}) ->
  {B.at(A, d, B.set_at(A, g, T.Pos{x, y}, v), T.Pos{qx, qy}) == B.at(A, d, g, T.Pos{qx, qy}) : A}:
  match b:
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, A>>,
        List.get(&2, List<&2, A>, List.set(&2, List<&2, A>, g, y, List.set(&2, A, row_of(A, g, y), x, v)), qy),
        List.get(&2, List<&2, A>, g, qy),
        get_set_ne(List<&2, A>, g, y, qy, List.set(&2, A, row_of(A, g, y), x, v), be)) :
        {Maybe.default(&2, A, List.get(&2, A, Maybe.default(&2, List<&2, A>, _, Nil{}), qx), d)
          == B.at(A, d, g, T.Pos{qx, qy}) : A}
      {==}
    case True{}:
      +yq = P.eq_sound(y, qy, be)
      %yq : {B.at(A, d, B.set_at(A, g, T.Pos{x, y}, v), T.Pos{qx, _}) == B.at(A, d, g, T.Pos{qx, _}) : A}
      at_set_ne.row(A, g, x, y, qx, v, d,
        {%P.and_true_r_id(Nat.is_eq(x, qx)) : {_ == False{} : Bool};
          %be : {Bool.and(Nat.is_eq(x, qx), _) == False{} : Bool};
          ne : {Nat.is_eq(x, qx) == False{} : Bool}},
        Nat.is_lt(y, List.length(&2, List<&2, A>, g)), {==})

# Setting p leaves every other cell as it was.
law at_set_ne:
  for -A: Data
  for +g: T.Grid(A)
  for +p: T.Pos
  for +q: T.Pos
  for +v: A
  for +d: A
  for ne: {B.same(p, q) == False{} : Bool}
  {B.at(A, d, B.set_at(A, g, p, v), q) == B.at(A, d, g, q) : A}

def at_set_ne(A, g, p, q, v, d, ne):
  match p q:
    case T.Pos{x, y} T.Pos{qx, qy}:
      at_set_ne.go(A, g, x, y, qx, qy, v, d, ne, Nat.is_eq(y, qy), {==})

law rows_wide_set:
  for -A: Data
  for +w: Nat
  for +g: T.Grid(A)
  for +y: Nat
  for +x: Nat
  for +v: A
  for +wide: {B.rows_wide(A, w, g) == True{} : Bool}
  {B.rows_wide(A, w, List.set(&2, List<&2, A>, g, y, List.set(&2, A, row_of(A, g, y), x, v))) == True{} : Bool}

def rows_wide_set(A, w, g, y, x, v, wide):
  match g y:
    case Nil{} _:
      {==}
    case r <> t 0n:
      %Equal.sym(Nat, List.length(&2, A, List.set(&2, A, r, x, v)), List.length(&2, A, r), set_len(A, r, x, v)) :
        {Bool.and(Nat.is_eq(_, w), B.rows_wide(A, w, t)) == True{} : Bool}
      wide
    case r <> t 1n+k:
      %Equal.sym(Bool, B.rows_wide(A, w, List.set(&2, List<&2, A>, t, k, List.set(&2, A, row_of(A, t, k), x, v))),
        True{}, rows_wide_set(A, w, t, k, x, v,
          P.and_true_r(Nat.is_eq(List.length(&2, A, r), w), B.rows_wide(A, w, t), wide))) :
        {Bool.and(Nat.is_eq(List.length(&2, A, r), w), _) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(Nat.is_eq(List.length(&2, A, r), w), True{}), Nat.is_eq(List.length(&2, A, r), w),
        P.and_true_r_id(Nat.is_eq(List.length(&2, A, r), w))) : {_ == True{} : Bool}
      P.and_true_l(Nat.is_eq(List.length(&2, A, r), w), B.rows_wide(A, w, t), wide)

law shaped_set:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(A)
  for +p: T.Pos
  for +v: A
  for +sh: {B.shaped(A, w, h, g) == True{} : Bool}
  {B.shaped(A, w, h, B.set_at(A, g, p, v)) == True{} : Bool}

def shaped_set(A, w, h, g, p, v, sh):
  match p:
    case T.Pos{x, y}:
      +r2 = List.set(&2, A, row_of(A, g, y), x, v)
      %Equal.sym(Nat, List.length(&2, List<&2, A>, List.set(&2, List<&2, A>, g, y, r2)),
        List.length(&2, List<&2, A>, g), set_len(List<&2, A>, g, y, r2)) :
        {Bool.and(Nat.is_eq(_, h), B.rows_wide(A, w, List.set(&2, List<&2, A>, g, y, r2))) == True{} : Bool}
      %Equal.sym(Bool, B.rows_wide(A, w, List.set(&2, List<&2, A>, g, y, r2)), True{},
        rows_wide_set(A, w, g, y, x, v, shaped_wide(A, w, h, g, sh))) :
        {Bool.and(Nat.is_eq(List.length(&2, List<&2, A>, g), h), _) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(Nat.is_eq(List.length(&2, List<&2, A>, g), h), True{}),
        Nat.is_eq(List.length(&2, List<&2, A>, g), h),
        P.and_true_r_id(Nat.is_eq(List.length(&2, List<&2, A>, g), h))) : {_ == True{} : Bool}
      P.and_true_l(Nat.is_eq(List.length(&2, List<&2, A>, g), h), B.rows_wide(A, w, g), sh)

# The blank grid
# ==============

law rep_len:
  for -A: Data
  for +n: Nat
  for +v: A
  {List.length(&2, A, List.replicate(A, n, v)) == n : Nat}

def rep_len(A, n, v):
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, List.length(&2, A, List.replicate(A, k, v)), k, rep_len(A, k, v)) :
        {1n+_ == 1n+k : Nat}
      {==}

law rep_wide:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +v: A
  {B.rows_wide(A, w, List.replicate(List<&2, A>, h, List.replicate(A, w, v))) == True{} : Bool}

def rep_wide(A, w, h, v):
  match h:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, List.length(&2, A, List.replicate(A, w, v)), w, rep_len(A, w, v)) :
        {Bool.and(Nat.is_eq(_, w), B.rows_wide(A, w, List.replicate(List<&2, A>, k, List.replicate(A, w, v))))
          == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(w, w), True{}, P.eq_refl(w)) :
        {Bool.and(_, B.rows_wide(A, w, List.replicate(List<&2, A>, k, List.replicate(A, w, v)))) == True{} : Bool}
      rep_wide(A, w, k, v)

law blank_shaped:
  for -A: Data
  for +w: Nat
  for +h: Nat
  for +v: A
  {B.shaped(A, w, h, B.blank(A, w, h, v)) == True{} : Bool}

def blank_shaped(A, w, h, v):
  %Equal.sym(Nat, List.length(&2, List<&2, A>, List.replicate(List<&2, A>, h, List.replicate(A, w, v))), h,
    rep_len(List<&2, A>, h, List.replicate(A, w, v))) :
    {Bool.and(Nat.is_eq(_, h), B.rows_wide(A, w, B.blank(A, w, h, v))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(h, h), True{}, P.eq_refl(h)) :
    {Bool.and(_, B.rows_wide(A, w, B.blank(A, w, h, v))) == True{} : Bool}
  rep_wide(A, w, h, v)

law rep_default:
  for -A: Data
  for +n: Nat
  for +v: A
  for +i: Nat
  {Maybe.default(&2, A, List.get(&2, A, List.replicate(A, n, v), i), v) == v : A}

def rep_default(A, n, v, i):
  match n i:
    case 0n _:
      {==}
    case 1n+k 0n:
      {==}
    case 1n+k 1n+j:
      rep_default(A, k, v, j)

law blank_at:
  for +w: Nat
  for +h: Nat
  for +x: Nat
  for +y: Nat
  {B.at(Bool, False{}, B.blank(Bool, w, h, False{}), T.Pos{x, y}) == False{} : Bool}

def blank_at(w, h, x, y):
  match h y:
    case 0n _:
      {==}
    case 1n+k 0n:
      rep_default(Bool, w, False{}, x)
    case 1n+k 1n+j:
      blank_at(w, k, x, j)

# Counting unrevealed cells
# =========================

law row_false_set:
  for +r: List<&2, Bool>
  for +x: Nat
  for e: {List.get(&2, Bool, r, x) == Some{False{}} : Maybe<&2, Bool>}
  {B.row_false(r) == 1n+B.row_false(List.set(&2, Bool, r, x, True{})) : Nat}

def row_false_set(r, x, e):
  match r x:
    case Nil{} _:
      Empty.absurd({0n == 1n+0n : Nat}, none_ne_some(Bool, False{}, e))
    case b <> t 0n:
      %Equal.sym(Bool, b, False{}, some_inj(Bool, b, False{}, e)) :
        {Nat.add(Bool.pick(Nat, _, 0n, 1n), B.row_false(t)) == 1n+Nat.add(0n, B.row_false(t)) : Nat}
      {==}
    case b <> t 1n+k:
      %Equal.sym(Nat, B.row_false(t), 1n+B.row_false(List.set(&2, Bool, t, k, True{})), row_false_set(t, k, e)) :
        {Nat.add(Bool.pick(Nat, b, 0n, 1n), _)
          == 1n+Nat.add(Bool.pick(Nat, b, 0n, 1n), B.row_false(List.set(&2, Bool, t, k, True{}))) : Nat}
      P.add_succ(Bool.pick(Nat, b, 0n, 1n), B.row_false(List.set(&2, Bool, t, k, True{})))

law count_false_set.go:
  for +g: T.Grid(Bool)
  for +y: Nat
  for +r: List<&2, Bool>
  for +r2: List<&2, Bool>
  for e: {List.get(&2, List<&2, Bool>, g, y) == Some{r} : Maybe<&2, List<&2, Bool>>}
  for rf: {B.row_false(r) == 1n+B.row_false(r2) : Nat}
  {B.count_false(g) == 1n+B.count_false(List.set(&2, List<&2, Bool>, g, y, r2)) : Nat}

def count_false_set.go(g, y, r, r2, e, rf):
  match g y:
    case Nil{} _:
      Empty.absurd({0n == 1n+0n : Nat}, none_ne_some(List<&2, Bool>, r, e))
    case row <> t 0n:
      %Equal.sym(List<&2, Bool>, row, r, some_inj(List<&2, Bool>, row, r, e)) :
        {Nat.add(B.row_false(_), B.count_false(t)) == 1n+Nat.add(B.row_false(r2), B.count_false(t)) : Nat}
      %Equal.sym(Nat, B.row_false(r), 1n+B.row_false(r2), rf) :
        {Nat.add(_, B.count_false(t)) == 1n+Nat.add(B.row_false(r2), B.count_false(t)) : Nat}
      {==}
    case row <> t 1n+k:
      %Equal.sym(Nat, B.count_false(t), 1n+B.count_false(List.set(&2, List<&2, Bool>, t, k, r2)),
        count_false_set.go(t, k, r, r2, e, rf)) :
        {Nat.add(B.row_false(row), _)
          == 1n+Nat.add(B.row_false(row), B.count_false(List.set(&2, List<&2, Bool>, t, k, r2))) : Nat}
      P.add_succ(B.row_false(row), B.count_false(List.set(&2, List<&2, Bool>, t, k, r2)))

# Revealing an unrevealed cell of the board uses up one count.
law count_false_set:
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(Bool)
  for +x: Nat
  for +y: Nat
  for +sh: {B.shaped(Bool, w, h, g) == True{} : Bool}
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  for hid: {B.at(Bool, False{}, g, T.Pos{x, y}) == False{} : Bool}
  {B.count_false(g) == 1n+B.count_false(B.set_at(Bool, g, T.Pos{x, y}, True{})) : Nat}

def count_false_set(w, h, g, x, y, sh, on, hid):
  +xw = P.and_true_l(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +yh = P.and_true_r(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +row = row_of(Bool, g, y)
  +xl = {%Equal.sym(Nat, List.length(&2, Bool, row), w, row_in_len(Bool, w, h, g, y, sh, yh)) :
    {Nat.is_lt(x, _) == True{} : Bool};
    xw : {Nat.is_lt(x, List.length(&2, Bool, row)) == True{} : Bool}}
  +cell = {%hid : {List.get(&2, Bool, row, x) == Some{_} : Maybe<&2, Bool>};
    get_in(Bool, row, x, False{}, xl) : {List.get(&2, Bool, row, x) == Some{False{}} : Maybe<&2, Bool>}}
  count_false_set.go(g, y, row, List.set(&2, Bool, row, x, True{}), row_in_get(Bool, w, h, g, y, sh, yh),
    row_false_set(row, x, cell))

# A grid with no unrevealed cell has every cell of the board revealed.
law count_false_zero:
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(Bool)
  for +x: Nat
  for +y: Nat
  for +sh: {B.shaped(Bool, w, h, g) == True{} : Bool}
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  for z: {B.count_false(g) == 0n : Nat}
  {B.at(Bool, False{}, g, T.Pos{x, y}) == True{} : Bool}

def count_false_zero.go(+w: Nat, +h: Nat, +g: T.Grid(Bool), +x: Nat, +y: Nat,
  +sh: {B.shaped(Bool, w, h, g) == True{} : Bool}, +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool},
  z: {B.count_false(g) == 0n : Nat}, +b: Bool, e: {B.at(Bool, False{}, g, T.Pos{x, y}) == b : Bool}) ->
  {B.at(Bool, False{}, g, T.Pos{x, y}) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      Empty.absurd({B.at(Bool, False{}, g, T.Pos{x, y}) == True{} : Bool},
        P.succ_ne_zero(B.count_false(B.set_at(Bool, g, T.Pos{x, y}, True{})),
          Equal.trans(Nat, 1n+B.count_false(B.set_at(Bool, g, T.Pos{x, y}, True{})), B.count_false(g), 0n,
            Equal.sym(Nat, B.count_false(g), 1n+B.count_false(B.set_at(Bool, g, T.Pos{x, y}, True{})),
              count_false_set(w, h, g, x, y, sh, on, e)), z)))

def count_false_zero(w, h, g, x, y, sh, on, z):
  count_false_zero.go(w, h, g, x, y, sh, on, z, B.at(Bool, False{}, g, T.Pos{x, y}), {==})
