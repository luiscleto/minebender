import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG

# Lemmas about board generation.

# Shape
# =====

law gen_row_len:
  for +z: G.Zone
  for +y: Nat
  for +xs: List<&2, Nat>
  for +st: G.GenState
  {List.length(&2, Bool, G.gen.row(z, y, xs, st)) == List.length(&2, Nat, xs) : Nat}

def gen_row_len(z, y, xs, st):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %gen_row_len(z, y, t, G.gen.next(z, T.Pos{x, y}, st)) :
        {1n+List.length(&2, Bool, G.gen.row(z, y, t, G.gen.next(z, T.Pos{x, y}, st)))
          == 1n+_ : Nat}
      {==}

law gen_rows_len:
  for +z: G.Zone
  for +w: Nat
  for +ys: List<&2, Nat>
  for +st: G.GenState
  {List.length(&2, List<&2, Bool>, G.gen.rows(z, w, ys, st)) == List.length(&2, Nat, ys) : Nat}

def gen_rows_len(z, w, ys, st):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +st2 = G.gen.row_state(z, y, List.range(w), st)
      %gen_rows_len(z, w, t, st2) :
        {1n+List.length(&2, List<&2, Bool>, G.gen.rows(z, w, t, st2)) == 1n+_ : Nat}
      {==}

law gen_rows_wide:
  for +z: G.Zone
  for +w: Nat
  for +ys: List<&2, Nat>
  for +st: G.GenState
  {L.rows_wide(Bool, w, G.gen.rows(z, w, ys, st)) == True{} : Bool}

def gen_rows_wide(z, w, ys, st):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +row = G.gen.row(z, y, List.range(w), st)
      +st2 = G.gen.row_state(z, y, List.range(w), st)
      +len = Equal.trans(Nat, List.length(&2, Bool, row), List.length(&2, Nat, List.range(w)), w,
        gen_row_len(z, y, List.range(w), st), P.range_length(w))
      %Equal.sym(Nat, List.length(&2, Bool, row), w, len) :
        {Bool.and(Nat.is_eq(_, w), L.rows_wide(Bool, w, G.gen.rows(z, w, t, st2))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(w, w), True{}, P.eq_refl(w)) :
        {Bool.and(_, L.rows_wide(Bool, w, G.gen.rows(z, w, t, st2))) == True{} : Bool}
      gen_rows_wide(z, w, t, st2)

# The zone a board of n mines keeps free around the first click.
def zone(+w: Nat, +h: Nat, +n: Nat, +first: T.Pos) -> G.Zone:
  G.Zone{first, Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h))}

law gen_shape_:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +first: T.Pos
  for +rs: List<&2, U32>
  {L.shaped(Bool, w, h, G.place_mines(w, h, n, first, rs)) == True{} : Bool}

def gen_shape_(w, h, n, first, rs):
  +z = zone(w, h, n, first)
  +st = {G.GenState{n, G.gen.left(z, B.cells(w, h)), rs} : G.GenState}
  +g = G.gen.rows(z, w, List.range(h), st)
  +len = Equal.trans(Nat, List.length(&2, List<&2, Bool>, g), List.length(&2, Nat, List.range(h)), h,
    gen_rows_len(z, w, List.range(h), st), P.range_length(h))
  %Equal.sym(Nat, List.length(&2, List<&2, Bool>, g), h, len) :
    {Bool.and(Nat.is_eq(_, h), L.rows_wide(Bool, w, g)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(h, h), True{}, P.eq_refl(h)) :
    {Bool.and(_, L.rows_wide(Bool, w, g)) == True{} : Bool}
  gen_rows_wide(z, w, List.range(h), st)

# The first click
# ===============

def gen_bit_first(+z: G.Zone, +p: T.Pos, +st: G.GenState,
  s: {G.gen.out(z, p) == True{} : Bool}) -> {G.gen.bit(z, p, st) == False{} : Bool}:
  match st:
    case G.GenState{need, left, rs}:
      %Equal.sym(Bool, G.gen.out(z, p), True{}, s) :
        {Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)), G.gen.pick(need, left, rs))
          == False{} : Bool}
      {==}

# A cell of a generated row that is in the zone has no mine.
law gen_row_first:
  for +z: G.Zone
  for +y: Nat
  for +xs: List<&2, Nat>
  for +j: Nat
  for +x: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, xs, j) == Some{x} : Maybe<&2, Nat>}
  for +s: {G.gen.out(z, T.Pos{x, y}) == True{} : Bool}
  {List.get(&2, Bool, G.gen.row(z, y, xs, st), j) == Some{False{}} : Maybe<&2, Bool>}

def gen_row_first(z, y, xs, j, x, st, e, s):
  match xs j:
    case Nil{} _:
      Empty.absurd({List.get(&2, Bool, G.gen.row(z, y, Nil{}, st), j) == Some{False{}}
        : Maybe<&2, Bool>}, PG.know_row_get.none(Nat, x, e))
    case a <> t 0n:
      %Equal.sym(Nat, a, x, PG.know_row_get.some(Nat, a, x, e)) :
        {Some{G.gen.bit(z, T.Pos{_, y}, st)} == Some{False{}} : Maybe<&2, Bool>}
      %Equal.sym(Bool, G.gen.bit(z, T.Pos{x, y}, st), False{},
        gen_bit_first(z, T.Pos{x, y}, st, s)) :
        {Some{_} == Some{False{}} : Maybe<&2, Bool>}
      {==}
    case a <> t 1n+k:
      gen_row_first(z, y, t, k, x, G.gen.next(z, T.Pos{a, y}, st), e, s)

def Maybe.disc_some(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{v}:
      Unit

def gen_some_ne_none(-A: Data, -a: A, e: {Some{a} == None{} : Maybe<&2, A>}) -> Empty:
  %e : Maybe.disc_some(A, _)
  Unit{}

law gen_row_out:
  for +z: G.Zone
  for +y: Nat
  for +xs: List<&2, Nat>
  for +j: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, xs, j) == None{} : Maybe<&2, Nat>}
  {List.get(&2, Bool, G.gen.row(z, y, xs, st), j) == None{} : Maybe<&2, Bool>}

def gen_row_out(z, y, xs, j, st, e):
  match xs j:
    case Nil{} _:
      {==}
    case a <> t 0n:
      Empty.absurd({List.get(&2, Bool, G.gen.row(z, y, a <> t, st), 0n) == None{}
        : Maybe<&2, Bool>}, gen_some_ne_none(Nat, a, e))
    case a <> t 1n+k:
      gen_row_out(z, y, t, k, G.gen.next(z, T.Pos{a, y}, st), e)

law gen_rows_get:
  for +z: G.Zone
  for +w: Nat
  for +ys: List<&2, Nat>
  for +i: Nat
  for +y: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, ys, i) == Some{y} : Maybe<&2, Nat>}
  exs st2: G.GenState
  {List.get(&2, List<&2, Bool>, G.gen.rows(z, w, ys, st), i)
    == Some{G.gen.row(z, y, List.range(w), st2)} : Maybe<&2, List<&2, Bool>>}

def gen_rows_get(z, w, ys, i, y, st, e):
  match ys i:
    case Nil{} _:
      Empty.absurd(Exists(G.GenState, st2 => {List.get(&2, List<&2, Bool>,
        G.gen.rows(z, w, Nil{}, st), i) == Some{G.gen.row(z, y, List.range(w), st2)}
        : Maybe<&2, List<&2, Bool>>}), PG.know_row_get.none(Nat, y, e))
    case a <> t 0n:
      %PG.know_row_get.some(Nat, a, y, e) :
        Exists(G.GenState, st2 => {Some{G.gen.row(z, a, List.range(w), st)}
          == Some{G.gen.row(z, _, List.range(w), st2)} : Maybe<&2, List<&2, Bool>>})
      (st, {==})
    case a <> t 1n+k:
      gen_rows_get(z, w, t, k, y, G.gen.row_state(z, a, List.range(w), st), e)

law gen_rows_out:
  for +z: G.Zone
  for +w: Nat
  for +ys: List<&2, Nat>
  for +i: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, ys, i) == None{} : Maybe<&2, Nat>}
  {List.get(&2, List<&2, Bool>, G.gen.rows(z, w, ys, st), i) == None{}
    : Maybe<&2, List<&2, Bool>>}

def gen_rows_out(z, w, ys, i, st, e):
  match ys i:
    case Nil{} _:
      {==}
    case a <> t 0n:
      Empty.absurd({List.get(&2, List<&2, Bool>, G.gen.rows(z, w, a <> t, st), 0n) == None{}
        : Maybe<&2, List<&2, Bool>>}, gen_some_ne_none(Nat, a, e))
    case a <> t 1n+k:
      gen_rows_out(z, w, t, k, G.gen.row_state(z, a, List.range(w), st), e)

def gen_first.col(+z: G.Zone, +fx: Nat, +fy: Nat, +w: Nat, +st2: G.GenState,
  s: {G.gen.out(z, T.Pos{fx, fy}) == True{} : Bool}, +b: Bool,
  e: {Nat.is_lt(fx, w) == b : Bool}) ->
  {Maybe.default(&2, Bool, List.get(&2, Bool, G.gen.row(z, fy, List.range(w), st2), fx), False{})
    == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Bool>, List.get(&2, Bool, G.gen.row(z, fy, List.range(w), st2), fx),
        Some{False{}},
        gen_row_first(z, fy, List.range(w), fx, fx, st2, P.range_get(w, fx, e), s)) :
        {Maybe.default(&2, Bool, _, False{}) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Bool>, List.get(&2, Bool, G.gen.row(z, fy, List.range(w), st2), fx),
        None{}, gen_row_out(z, fy, List.range(w), fx, st2, P.range_get_out(w, fx, e))) :
        {Maybe.default(&2, Bool, _, False{}) == False{} : Bool}
      {==}

def gen_first.found(+z: G.Zone, +fx: Nat, +fy: Nat, +w: Nat, +g: T.Grid(Bool),
  s: {G.gen.out(z, T.Pos{fx, fy}) == True{} : Bool},
  r: Exists(G.GenState, st2 => {List.get(&2, List<&2, Bool>, g, fy)
    == Some{G.gen.row(z, fy, List.range(w), st2)} : Maybe<&2, List<&2, Bool>>})) ->
  {L.mine(g, T.Pos{fx, fy}) == False{} : Bool}:
  match r:
    case (st2, eq):
      %Equal.sym(Maybe<&2, List<&2, Bool>>, List.get(&2, List<&2, Bool>, g, fy),
        Some{G.gen.row(z, fy, List.range(w), st2)}, eq) :
        {Maybe.default(&2, Bool, List.get(&2, Bool,
          Maybe.default(&2, List<&2, Bool>, _, Nil{}), fx), False{}) == False{} : Bool}
      gen_first.col(z, fx, fy, w, st2, s, Nat.is_lt(fx, w), {==})

def gen_first.row(+z: G.Zone, +fx: Nat, +fy: Nat, +w: Nat, +h: Nat, +st: G.GenState,
  s: {G.gen.out(z, T.Pos{fx, fy}) == True{} : Bool}, +b: Bool,
  e: {Nat.is_lt(fy, h) == b : Bool}) ->
  {L.mine(G.gen.rows(z, w, List.range(h), st), T.Pos{fx, fy}) == False{} : Bool}:
  match b:
    case True{}:
      gen_first.found(z, fx, fy, w, G.gen.rows(z, w, List.range(h), st), s,
        gen_rows_get(z, w, List.range(h), fy, fy, st, P.range_get(h, fy, e)))
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, Bool>>,
        List.get(&2, List<&2, Bool>, G.gen.rows(z, w, List.range(h), st), fy), None{},
        gen_rows_out(z, w, List.range(h), fy, st, P.range_get_out(h, fy, e))) :
        {Maybe.default(&2, Bool, List.get(&2, Bool,
          Maybe.default(&2, List<&2, Bool>, _, Nil{}), fx), False{}) == False{} : Bool}
      {==}

law sub_self:
  for +a: Nat
  {Nat.sub(a, a) == 0n : Nat}

def sub_self(a):
  match a:
    case 0n:
      {==}
    case 1n+k:
      sub_self(k)

# A cell is within one step of itself.
law within_self:
  for +p: T.Pos
  {B.within_one(p, p) == True{} : Bool}

def within_self(p):
  match p:
    case T.Pos{x, y}:
      %Equal.sym(Nat, Nat.sub(x, x), 0n, sub_self(x)) :
        {Bool.and(Nat.is_le(Nat.add(_, _), 1n), Nat.is_le(Nat.add(Nat.sub(y, y), Nat.sub(y, y)), 1n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(y, y), 0n, sub_self(y)) :
        {Bool.and(Nat.is_le(Nat.add(0n, 0n), 1n), Nat.is_le(Nat.add(_, _), 1n)) == True{} : Bool}
      {==}

# The first click is always in its own zone.
law out_first:
  for +first: T.Pos
  for +wide: Bool
  {G.gen.out(G.Zone{first, wide}, first) == True{} : Bool}

def out_first(first, wide):
  match wide:
    case True{}:
      within_self(first)
    case False{}:
      PG.same_refl(first)

law gen_first_safe_:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +first: T.Pos
  for +rs: List<&2, U32>
  {L.mine(G.place_mines(w, h, n, first, rs), first) == False{} : Bool}

def gen_first_safe_(w, h, n, first, rs):
  match first:
    case T.Pos{fx, fy}:
      +p = {T.Pos{fx, fy} : T.Pos}
      +z = zone(w, h, n, p)
      gen_first.row(z, fx, fy, w, h,
        {G.GenState{n, G.gen.left(z, B.cells(w, h)), rs} : G.GenState},
        out_first(p, Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h))), Nat.is_lt(fy, h), {==})

law within_eq:
  for +p: T.Pos
  for +q: T.Pos
  {B.within_one(p, q) == L.within_one(p, q) : Bool}

def within_eq(p, q):
  match p q:
    case T.Pos{px, py} T.Pos{qx, qy}:
      {==}

# A wide zone holds every cell next to the first click.
def opening_in(+first: T.Pos, +p: T.Pos, +wide: Bool, ew: {wide == True{} : Bool},
  near: {L.within_one(first, p) == True{} : Bool}) -> {G.gen.out(G.Zone{first, wide}, p) == True{} : Bool}:
  %Equal.sym(Bool, wide, True{}, ew) : {G.gen.out(G.Zone{first, _}, p) == True{} : Bool}
  Equal.trans(Bool, B.within_one(first, p), L.within_one(first, p), True{}, within_eq(first, p), near)

# With room, no cell next to the first click gets a mine.
law gen_opening_:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +first: T.Pos
  for +rs: List<&2, U32>
  for +room: {Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h)) == True{} : Bool}
  for +q: T.Pos
  for +near: {L.within_one(first, q) == True{} : Bool}
  {L.mine(G.place_mines(w, h, n, first, rs), q) == False{} : Bool}

def gen_opening_(w, h, n, first, rs, room, q, near):
  match q:
    case T.Pos{qx, qy}:
      +p = {T.Pos{qx, qy} : T.Pos}
      +z = zone(w, h, n, first)
      gen_first.row(z, qx, qy, w, h,
        {G.GenState{n, G.gen.left(z, B.cells(w, h)), rs} : G.GenState},
        opening_in(first, p, Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h)), room, near), Nat.is_lt(qy, h), {==})

# Exactly n mines
# ===============

def st_need(st: G.GenState) -> Nat:
  match st:
    case G.GenState{need, left, rs}:
      need

def st_left(st: G.GenState) -> Nat:
  match st:
    case G.GenState{need, left, rs}:
      left

def one(b: Bool) -> Nat:
  Bool.pick(Nat, b, 1n, 0n)

# What one cell does to the state: the mines placed plus the mines still
# needed stay the same, need <= left stays true, and left counts down for
# every cell outside the zone.
def GenStep(+z: G.Zone, +p: T.Pos, +st: G.GenState, +lp: Nat) -> Type:
  {Nat.add(one(G.gen.bit(z, p, st)), st_need(G.gen.next(z, p, st))) == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.next(z, p, st)), st_left(G.gen.next(z, p, st))) == True{} : Bool} &
  {st_left(G.gen.next(z, p, st)) == lp : Nat}

def gen_pick_false(+need: Nat, +left: Nat, +rs: List<&2, U32>,
  e: {G.gen.pick(need, left, rs) == False{} : Bool}) -> {Nat.is_eq(need, left) == False{} : Bool}:
  match rs:
    case Nil{}:
      e
    case r <> t:
      P.or_false_inv(Nat.is_eq(need, left), G.gen.coin(r, left, need), e)

def gen_take(+z: G.Zone, +p: T.Pos, +m: Nat, +lp: Nat, +rs: List<&2, U32>,
  inv: {Nat.is_le(1n+m, 1n+lp) == True{} : Bool}, +c: Bool,
  ce: {G.gen.pick(1n+m, 1n+lp, rs) == c : Bool}) ->
  {Nat.add(one(c), Nat.sub(1n+m, one(c))) == 1n+m : Nat} &
  {Nat.is_le(Nat.sub(1n+m, one(c)), Nat.sub(1n+lp, 1n)) == True{} : Bool} &
  {Nat.sub(1n+lp, 1n) == lp : Nat}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, P.sub_zero(m)) :
        {1n+_ == 1n+m : Nat} & {Nat.is_le(_, Nat.sub(lp, 0n)) == True{} : Bool} &
        {Nat.sub(lp, 0n) == lp : Nat}
      %Equal.sym(Nat, Nat.sub(lp, 0n), lp, P.sub_zero(lp)) :
        {1n+m == 1n+m : Nat} & {Nat.is_le(m, _) == True{} : Bool} & {_ == lp : Nat}
      ({==}, (inv, {==}))
    case False{}:
      %Equal.sym(Nat, Nat.sub(lp, 0n), lp, P.sub_zero(lp)) :
        {1n+m == 1n+m : Nat} & {Nat.is_le(1n+m, _) == True{} : Bool} & {_ == lp : Nat}
      ({==}, (P.le_ne(m, lp, inv, gen_pick_false(1n+m, 1n+lp, rs, ce)), {==}))

def gen_cell.need(+z: G.Zone, +p: T.Pos, +need: Nat, +lp: Nat, +rs: List<&2, U32>,
  inv: {Nat.is_le(need, 1n+lp) == True{} : Bool}) ->
  {Nat.add(one(Bool.and(Nat.is_lt(0n, need), G.gen.pick(need, 1n+lp, rs))),
     Nat.sub(need, one(Bool.and(Nat.is_lt(0n, need), G.gen.pick(need, 1n+lp, rs))))) == need : Nat} &
  {Nat.is_le(Nat.sub(need, one(Bool.and(Nat.is_lt(0n, need), G.gen.pick(need, 1n+lp, rs)))),
     Nat.sub(1n+lp, 1n)) == True{} : Bool} &
  {Nat.sub(1n+lp, 1n) == lp : Nat}:
  match need:
    case 0n:
      %Equal.sym(Nat, Nat.sub(lp, 0n), lp, P.sub_zero(lp)) :
        {0n == 0n : Nat} & {Nat.is_le(0n, _) == True{} : Bool} & {_ == lp : Nat}
      ({==}, (P.le_zero_l(lp), {==}))
    case 1n+m:
      gen_take(z, p, m, lp, rs, inv, G.gen.pick(1n+m, 1n+lp, rs), {==})

def gen_cell.go(+z: G.Zone, +p: T.Pos, +need: Nat, +left: Nat, +rs: List<&2, U32>, +lp: Nat,
  inv: {Nat.is_le(need, left) == True{} : Bool}, +s: Bool, e: {G.gen.out(z, p) == s : Bool},
  +lft: {left == Nat.add(Bool.pick(Nat, s, 0n, 1n), lp) : Nat}) ->
  GenStep(z, p, G.GenState{need, left, rs}, lp):
  match s:
    case True{}:
      %Equal.sym(Bool, G.gen.out(z, p), True{}, e) :
        {Nat.add(one(Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)), G.gen.pick(need, left, rs))),
          st_need(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs))) == need : Nat} &
        {Nat.is_le(st_need(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs)),
          st_left(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs))) == True{} : Bool} &
        {st_left(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs)) == lp : Nat}
      ({==}, (inv, lft))
    case False{}:
      %Equal.sym(Bool, G.gen.out(z, p), False{}, e) :
        {Nat.add(one(Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)), G.gen.pick(need, left, rs))),
          st_need(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs))) == need : Nat} &
        {Nat.is_le(st_need(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs)),
          st_left(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs))) == True{} : Bool} &
        {st_left(G.gen.next.go(_, Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)),
            G.gen.pick(need, left, rs)), need, left, rs)) == lp : Nat}
      %Equal.sym(Nat, left, 1n+lp, lft) :
        {Nat.add(one(Bool.and(Nat.is_lt(0n, need), G.gen.pick(need, _, rs))),
          Nat.sub(need, one(Bool.and(Nat.is_lt(0n, need), G.gen.pick(need, _, rs))))) == need : Nat} &
        {Nat.is_le(Nat.sub(need, one(Bool.and(Nat.is_lt(0n, need), G.gen.pick(need, _, rs)))),
          Nat.sub(_, 1n)) == True{} : Bool} &
        {Nat.sub(_, 1n) == lp : Nat}
      gen_cell.need(z, p, need, lp, rs,
        {%lft : {Nat.is_le(need, _) == True{} : Bool}; inv : {Nat.is_le(need, 1n+lp) == True{} : Bool}})


law gen_cell:
  for +z: G.Zone
  for +p: T.Pos
  for +st: G.GenState
  for +lp: Nat
  for inv: {Nat.is_le(st_need(st), st_left(st)) == True{} : Bool}
  for lft: {st_left(st) == Nat.add(Bool.pick(Nat, G.gen.out(z, p), 0n, 1n), lp) : Nat}
  GenStep(z, p, st, lp)

def gen_cell(z, p, st, lp, inv, lft):
  match st:
    case G.GenState{need, left, rs}:
      gen_cell.go(z, p, need, left, rs, lp, inv, G.gen.out(z, p), {==}, lft)

def gen_row_count.step(+z: G.Zone, +p: T.Pos, +st: G.GenState, +rm: Nat, +nf: Nat,
  s1: {Nat.add(one(G.gen.bit(z, p, st)), st_need(G.gen.next(z, p, st))) == st_need(st) : Nat},
  r1: {Nat.add(rm, nf) == st_need(G.gen.next(z, p, st)) : Nat}) ->
  {Nat.add(Nat.add(one(G.gen.bit(z, p, st)), rm), nf) == st_need(st) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(one(G.gen.bit(z, p, st)), rm), nf),
    Nat.add(one(G.gen.bit(z, p, st)), Nat.add(rm, nf)),
    P.add_assoc(one(G.gen.bit(z, p, st)), rm, nf)) : {_ == st_need(st) : Nat}
  %Equal.sym(Nat, Nat.add(rm, nf), st_need(G.gen.next(z, p, st)), r1) :
    {Nat.add(one(G.gen.bit(z, p, st)), _) == st_need(st) : Nat}
  s1

def gen_row_count.k2(+z: G.Zone, +y: Nat, +t: List<&2, Nat>, +p: T.Pos, +st: G.GenState,
  +cs: List<&2, T.Pos>,
  s1: {Nat.add(one(G.gen.bit(z, p, st)), st_need(G.gen.next(z, p, st))) == st_need(st) : Nat},
  r: {Nat.add(L.row_mines(G.gen.row(z, y, t, G.gen.next(z, p, st))),
       st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == st_need(G.gen.next(z, p, st)) : Nat} &
    {Nat.is_le(st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st))),
       st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == True{} : Bool} &
    {st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st))) == G.gen.left(z, cs) : Nat}) ->
  {Nat.add(Nat.add(one(G.gen.bit(z, p, st)), L.row_mines(G.gen.row(z, y, t, G.gen.next(z, p, st)))),
     st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st))),
     st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == True{} : Bool} &
  {st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st))) == G.gen.left(z, cs) : Nat}:
  match r:
    case (r1, rest):
      (gen_row_count.step(z, p, st,
        L.row_mines(G.gen.row(z, y, t, G.gen.next(z, p, st))),
        st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st))), s1, r1), rest)

def gen_row_count.k(+z: G.Zone, +y: Nat, +t: List<&2, Nat>, +p: T.Pos, +st: G.GenState,
  +cs: List<&2, T.Pos>,
  step: GenStep(z, p, st, G.gen.left(z, List.append(&2, T.Pos, B.row_cells(y, t), cs))),
  ih: ({Nat.is_le(st_need(G.gen.next(z, p, st)), st_left(G.gen.next(z, p, st))) == True{} : Bool} ->
    {st_left(G.gen.next(z, p, st)) == G.gen.left(z, List.append(&2, T.Pos, B.row_cells(y, t), cs)) : Nat} ->
    {Nat.add(L.row_mines(G.gen.row(z, y, t, G.gen.next(z, p, st))),
       st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == st_need(G.gen.next(z, p, st)) : Nat} &
    {Nat.is_le(st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st))),
       st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == True{} : Bool} &
    {st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st))) == G.gen.left(z, cs) : Nat})) ->
  {Nat.add(Nat.add(one(G.gen.bit(z, p, st)), L.row_mines(G.gen.row(z, y, t, G.gen.next(z, p, st)))),
     st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.row_state(z, y, t, G.gen.next(z, p, st))),
     st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st)))) == True{} : Bool} &
  {st_left(G.gen.row_state(z, y, t, G.gen.next(z, p, st))) == G.gen.left(z, cs) : Nat}:
  match step:
    case (s1, rest):
      match rest:
        case (s2, s3):
          gen_row_count.k2(z, y, t, p, st, cs, s1, ih(s2, s3))


law gen_row_count:
  for +z: G.Zone
  for +y: Nat
  for +xs: List<&2, Nat>
  for +st: G.GenState
  for +cs: List<&2, T.Pos>
  for inv: {Nat.is_le(st_need(st), st_left(st)) == True{} : Bool}
  for lft: {st_left(st) == G.gen.left(z, List.append(&2, T.Pos, B.row_cells(y, xs), cs)) : Nat}
  {Nat.add(L.row_mines(G.gen.row(z, y, xs, st)), st_need(G.gen.row_state(z, y, xs, st)))
    == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.row_state(z, y, xs, st)), st_left(G.gen.row_state(z, y, xs, st)))
    == True{} : Bool} &
  {st_left(G.gen.row_state(z, y, xs, st)) == G.gen.left(z, cs) : Nat}

def gen_row_count(z, y, xs, st, cs, inv, lft):
  match xs:
    case Nil{}:
      ({==}, (inv, lft))
    case x <> t:
      +p = {T.Pos{x, y} : T.Pos}
      +lp = G.gen.left(z, List.append(&2, T.Pos, B.row_cells(y, t), cs))
      +nx = G.gen.next(z, p, st)
      gen_row_count.k(z, y, t, p, st, cs, gen_cell(z, p, st, lp, inv, lft),
        s => gen_row_count(z, y, t, nx, cs, s))


def gen_rows_count.k(+z: G.Zone, +w: Nat, +y: Nat, +t: List<&2, Nat>, +st: G.GenState,
  r: {Nat.add(L.row_mines(G.gen.row(z, y, List.range(w), st)),
       st_need(G.gen.row_state(z, y, List.range(w), st))) == st_need(st) : Nat} &
    {Nat.is_le(st_need(G.gen.row_state(z, y, List.range(w), st)),
       st_left(G.gen.row_state(z, y, List.range(w), st))) == True{} : Bool} &
    {st_left(G.gen.row_state(z, y, List.range(w), st)) == G.gen.left(z, B.cells.go(w, t)) : Nat},
  ih: {Nat.is_le(st_need(G.gen.row_state(z, y, List.range(w), st)),
       st_left(G.gen.row_state(z, y, List.range(w), st))) == True{} : Bool} ->
    {st_left(G.gen.row_state(z, y, List.range(w), st)) == G.gen.left(z, B.cells.go(w, t)) : Nat} ->
    {L.total_mines(G.gen.rows(z, w, t, G.gen.row_state(z, y, List.range(w), st)))
      == st_need(G.gen.row_state(z, y, List.range(w), st)) : Nat}) ->
  {Nat.add(L.row_mines(G.gen.row(z, y, List.range(w), st)),
     L.total_mines(G.gen.rows(z, w, t, G.gen.row_state(z, y, List.range(w), st))))
    == st_need(st) : Nat}:
  match r:
    case (r1, rest):
      match rest:
        case (r2, r3):
          %Equal.sym(Nat, L.total_mines(G.gen.rows(z, w, t, G.gen.row_state(z, y, List.range(w), st))),
            st_need(G.gen.row_state(z, y, List.range(w), st)), ih(r2, r3)) :
            {Nat.add(L.row_mines(G.gen.row(z, y, List.range(w), st)), _) == st_need(st) : Nat}
          r1

law gen_rows_count:
  for +z: G.Zone
  for +w: Nat
  for +ys: List<&2, Nat>
  for +st: G.GenState
  for inv: {Nat.is_le(st_need(st), st_left(st)) == True{} : Bool}
  for lft: {st_left(st) == G.gen.left(z, B.cells.go(w, ys)) : Nat}
  {L.total_mines(G.gen.rows(z, w, ys, st)) == st_need(st) : Nat}

def gen_rows_count(z, w, ys, st, inv, lft):
  match ys:
    case Nil{}:
      Equal.sym(Nat, st_need(st), 0n, P.le_zero(st_need(st),
        {%lft : {Nat.is_le(st_need(st), _) == True{} : Bool};
          inv : {Nat.is_le(st_need(st), 0n) == True{} : Bool}}))
    case y <> t:
      +rs2 = G.gen.row_state(z, y, List.range(w), st)
      gen_rows_count.k(z, w, y, t, st,
        gen_row_count(z, y, List.range(w), st, B.cells.go(w, t), inv, lft),
        a => b => gen_rows_count(z, w, t, rs2, a, b))

# Counting the candidates
# =======================

# How many cells of ps are in the zone.
def outs(+z: G.Zone, ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> t:
      Nat.add(Bool.pick(Nat, G.gen.out(z, p), 1n, 0n), outs(z, t))

def gen_left_firsts.go(+z: G.Zone, +p: T.Pos, +t: List<&2, T.Pos>, +s: Bool,
  ih: {Nat.add(G.gen.left(z, t), outs(z, t)) == List.length(&2, T.Pos, t) : Nat}) ->
  {Nat.add(Nat.add(Bool.pick(Nat, s, 0n, 1n), G.gen.left(z, t)),
     Nat.add(Bool.pick(Nat, s, 1n, 0n), outs(z, t))) == 1n+List.length(&2, T.Pos, t) : Nat}:
  match s:
    case True{}:
      %Equal.sym(Nat, Nat.add(G.gen.left(z, t), 1n+outs(z, t)),
        1n+Nat.add(G.gen.left(z, t), outs(z, t)),
        P.add_succ(G.gen.left(z, t), outs(z, t))) :
        {_ == 1n+List.length(&2, T.Pos, t) : Nat}
      %Equal.sym(Nat, Nat.add(G.gen.left(z, t), outs(z, t)), List.length(&2, T.Pos, t), ih) :
        {1n+_ == 1n+List.length(&2, T.Pos, t) : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.add(G.gen.left(z, t), outs(z, t)), List.length(&2, T.Pos, t), ih) :
        {1n+_ == 1n+List.length(&2, T.Pos, t) : Nat}
      {==}

# Every cell is either a candidate or in the zone.
law gen_left_firsts:
  for +z: G.Zone
  for +ps: List<&2, T.Pos>
  {Nat.add(G.gen.left(z, ps), outs(z, ps)) == List.length(&2, T.Pos, ps) : Nat}

def gen_left_firsts(z, ps):
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      gen_left_firsts.go(z, p, t, G.gen.out(z, p), gen_left_firsts(z, t))

law firsts_append:
  for +z: G.Zone
  for +xs: List<&2, T.Pos>
  for +ys: List<&2, T.Pos>
  {outs(z, List.append(&2, T.Pos, xs, ys)) == Nat.add(outs(z, xs), outs(z, ys)) : Nat}

def firsts_append(z, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case p <> t:
      %Equal.sym(Nat, outs(z, List.append(&2, T.Pos, t, ys)),
        Nat.add(outs(z, t), outs(z, ys)), firsts_append(z, t, ys)) :
        {Nat.add(Bool.pick(Nat, G.gen.out(z, p), 1n, 0n), _)
          == Nat.add(Nat.add(Bool.pick(Nat, G.gen.out(z, p), 1n, 0n), outs(z, t)), outs(z, ys)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(Bool.pick(Nat, G.gen.out(z, p), 1n, 0n), outs(z, t)), outs(z, ys)),
        Nat.add(Bool.pick(Nat, G.gen.out(z, p), 1n, 0n), Nat.add(outs(z, t), outs(z, ys))),
        P.add_assoc(Bool.pick(Nat, G.gen.out(z, p), 1n, 0n), outs(z, t), outs(z, ys)))

# How many elements of xs are i.
def cnt(+i: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(Bool.pick(Nat, Nat.is_eq(x, i), 1n, 0n), cnt(i, t))

law cnt_append:
  for +i: Nat
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  {cnt(i, List.append(&2, Nat, xs, ys)) == Nat.add(cnt(i, xs), cnt(i, ys)) : Nat}

def cnt_append(i, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Nat, cnt(i, List.append(&2, Nat, t, ys)), Nat.add(cnt(i, t), cnt(i, ys)), cnt_append(i, t, ys)) :
        {Nat.add(Bool.pick(Nat, Nat.is_eq(x, i), 1n, 0n), _)
          == Nat.add(Nat.add(Bool.pick(Nat, Nat.is_eq(x, i), 1n, 0n), cnt(i, t)), cnt(i, ys)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(Bool.pick(Nat, Nat.is_eq(x, i), 1n, 0n), cnt(i, t)), cnt(i, ys)),
        Nat.add(Bool.pick(Nat, Nat.is_eq(x, i), 1n, 0n), Nat.add(cnt(i, t), cnt(i, ys))),
        P.add_assoc(Bool.pick(Nat, Nat.is_eq(x, i), 1n, 0n), cnt(i, t), cnt(i, ys)))

law cnt_step:
  for +i: Nat
  for +p: Nat
  {Nat.add(Bool.pick(Nat, Nat.is_lt(i, p), 1n, 0n), Nat.add(Bool.pick(Nat, Nat.is_eq(p, i), 1n, 0n), 0n))
    == Bool.pick(Nat, Nat.is_lt(i, 1n+p), 1n, 0n) : Nat}

def cnt_step(i, p):
  match i p:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+j 0n:
      %Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, P.lt_zero(j)) :
        {0n == Bool.pick(Nat, _, 1n, 0n) : Nat}
      {==}
    case 1n+j 1n+q:
      cnt_step(j, q)

# Each number below n appears in range(n) once.
law cnt_range:
  for +i: Nat
  for +n: Nat
  {cnt(i, List.range(n)) == Bool.pick(Nat, Nat.is_lt(i, n), 1n, 0n) : Nat}

def cnt_range(i, n):
  match n:
    case 0n:
      %Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)) :
        {0n == Bool.pick(Nat, _, 1n, 0n) : Nat}
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Nat>, List.range(1n+p), List.append(&2, Nat, List.range(p), [p]), P.range_snoc(p)) :
        {cnt(i, _) == Bool.pick(Nat, Nat.is_lt(i, 1n+p), 1n, 0n) : Nat}
      %Equal.sym(Nat, cnt(i, List.append(&2, Nat, List.range(p), [p])),
        Nat.add(cnt(i, List.range(p)), cnt(i, [p])), cnt_append(i, List.range(p), [p])) :
        {_ == Bool.pick(Nat, Nat.is_lt(i, 1n+p), 1n, 0n) : Nat}
      %Equal.sym(Nat, cnt(i, List.range(p)), Bool.pick(Nat, Nat.is_lt(i, p), 1n, 0n), cnt_range(i, p)) :
        {Nat.add(_, cnt(i, [p])) == Bool.pick(Nat, Nat.is_lt(i, 1n+p), 1n, 0n) : Nat}
      cnt_step(i, p)

def firsts_row.end(+a: Bool, +b: Bool, +c: Nat) ->
  {Nat.add(Bool.pick(Nat, Bool.and(a, b), 1n, 0n), Bool.pick(Nat, b, c, 0n))
    == Bool.pick(Nat, b, Nat.add(Bool.pick(Nat, a, 1n, 0n), c), 0n) : Nat}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def firsts_row.go(+fx: Nat, +fy: Nat, +y: Nat, +xs: List<&2, Nat>, +b: Bool,
  +e: {Nat.is_eq(y, fy) == b : Bool}) ->
  {outs(G.Zone{T.Pos{fx, fy}, False{}}, B.row_cells(y, xs)) == Bool.pick(Nat, b, cnt(fx, xs), 0n) : Nat}:
  match xs:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case x <> t:
      %Equal.sym(Bool, Nat.is_eq(y, fy), b, e) :
        {Nat.add(Bool.pick(Nat, Bool.and(Nat.is_eq(x, fx), _), 1n, 0n), outs(G.Zone{T.Pos{fx, fy}, False{}}, B.row_cells(y, t)))
          == Bool.pick(Nat, b, cnt(fx, x <> t), 0n) : Nat}
      %Equal.sym(Nat, outs(G.Zone{T.Pos{fx, fy}, False{}}, B.row_cells(y, t)), Bool.pick(Nat, b, cnt(fx, t), 0n),
        firsts_row.go(fx, fy, y, t, b, e)) :
        {Nat.add(Bool.pick(Nat, Bool.and(Nat.is_eq(x, fx), b), 1n, 0n), _)
          == Bool.pick(Nat, b, cnt(fx, x <> t), 0n) : Nat}
      firsts_row.end(Nat.is_eq(x, fx), b, cnt(fx, t))

def firsts_rows.go(+fx: Nat, +fy: Nat, +w: Nat, +y: Nat, +t: List<&2, Nat>,
  c1: {cnt(fx, List.range(w)) == 1n : Nat},
  ih: {outs(G.Zone{T.Pos{fx, fy}, False{}}, B.cells.go(w, t)) == cnt(fy, t) : Nat}) ->
  {outs(G.Zone{T.Pos{fx, fy}, False{}}, List.append(&2, T.Pos, B.row_cells(y, List.range(w)), B.cells.go(w, t)))
    == cnt(fy, y <> t) : Nat}:
  +row = B.row_cells(y, List.range(w))
  %Equal.sym(Nat, outs(G.Zone{T.Pos{fx, fy}, False{}}, List.append(&2, T.Pos, row, B.cells.go(w, t))),
    Nat.add(outs(G.Zone{T.Pos{fx, fy}, False{}}, row), outs(G.Zone{T.Pos{fx, fy}, False{}}, B.cells.go(w, t))),
    firsts_append(G.Zone{T.Pos{fx, fy}, False{}}, row, B.cells.go(w, t))) : {_ == cnt(fy, y <> t) : Nat}
  %Equal.sym(Nat, outs(G.Zone{T.Pos{fx, fy}, False{}}, row), Bool.pick(Nat, Nat.is_eq(y, fy), cnt(fx, List.range(w)), 0n),
    firsts_row.go(fx, fy, y, List.range(w), Nat.is_eq(y, fy), {==})) :
    {Nat.add(_, outs(G.Zone{T.Pos{fx, fy}, False{}}, B.cells.go(w, t))) == cnt(fy, y <> t) : Nat}
  %Equal.sym(Nat, cnt(fx, List.range(w)), 1n, c1) :
    {Nat.add(Bool.pick(Nat, Nat.is_eq(y, fy), _, 0n), outs(G.Zone{T.Pos{fx, fy}, False{}}, B.cells.go(w, t)))
      == cnt(fy, y <> t) : Nat}
  %Equal.sym(Nat, outs(G.Zone{T.Pos{fx, fy}, False{}}, B.cells.go(w, t)), cnt(fy, t), ih) :
    {Nat.add(Bool.pick(Nat, Nat.is_eq(y, fy), 1n, 0n), _) == cnt(fy, y <> t) : Nat}
  {==}

law firsts_rows:
  for +fx: Nat
  for +fy: Nat
  for +w: Nat
  for +ys: List<&2, Nat>
  for +c1: {cnt(fx, List.range(w)) == 1n : Nat}
  {outs(G.Zone{T.Pos{fx, fy}, False{}}, B.cells.go(w, ys)) == cnt(fy, ys) : Nat}

def firsts_rows(fx, fy, w, ys, c1):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      firsts_rows.go(fx, fy, w, y, t, c1, firsts_rows(fx, fy, w, t, c1))

law row_cells_len:
  for +y: Nat
  for +xs: List<&2, Nat>
  {List.length(&2, T.Pos, B.row_cells(y, xs)) == List.length(&2, Nat, xs) : Nat}

def row_cells_len(y, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Nat, List.length(&2, T.Pos, B.row_cells(y, t)), List.length(&2, Nat, t), row_cells_len(y, t)) :
        {1n+_ == 1n+List.length(&2, Nat, t) : Nat}
      {==}

law cells_go_len:
  for +w: Nat
  for +ys: List<&2, Nat>
  {List.length(&2, T.Pos, B.cells.go(w, ys)) == Nat.mul(List.length(&2, Nat, ys), w) : Nat}

def cells_go_len(w, ys):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +row = B.row_cells(y, List.range(w))
      %Equal.sym(Nat, List.length(&2, T.Pos, List.append(&2, T.Pos, row, B.cells.go(w, t))),
        Nat.add(List.length(&2, T.Pos, row), List.length(&2, T.Pos, B.cells.go(w, t))),
        P.length_append(T.Pos, row, B.cells.go(w, t))) :
        {_ == Nat.add(w, Nat.mul(List.length(&2, Nat, t), w)) : Nat}
      %Equal.sym(Nat, List.length(&2, T.Pos, row), w,
        Equal.trans(Nat, List.length(&2, T.Pos, row), List.length(&2, Nat, List.range(w)), w,
          row_cells_len(y, List.range(w)), P.range_length(w))) :
        {Nat.add(_, List.length(&2, T.Pos, B.cells.go(w, t))) == Nat.add(w, Nat.mul(List.length(&2, Nat, t), w)) : Nat}
      %Equal.sym(Nat, List.length(&2, T.Pos, B.cells.go(w, t)), Nat.mul(List.length(&2, Nat, t), w), cells_go_len(w, t)) :
        {Nat.add(w, _) == Nat.add(w, Nat.mul(List.length(&2, Nat, t), w)) : Nat}
      {==}

def one_when(+i: Nat, +n: Nat, lt: {Nat.is_lt(i, n) == True{} : Bool}) -> {cnt(i, List.range(n)) == 1n : Nat}:
  Equal.trans(Nat, cnt(i, List.range(n)), Bool.pick(Nat, Nat.is_lt(i, n), 1n, 0n), 1n,
    cnt_range(i, n),
    Equal.cong(Bool, Nat, b => Bool.pick(Nat, b, 1n, 0n), Nat.is_lt(i, n), True{}, lt))

# Arithmetic
# ==========

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e1: {Nat.is_le(a, b) == True{} : Bool}
  for e2: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def le_trans.k(+a: Nat, +b: Nat, +c: Nat, r1: P.LeW(a, b), r2: P.LeW(b, c)) -> {Nat.is_le(a, c) == True{} : Bool}:
  match r1:
    case (+k1, e1):
      match r2:
        case (+k2, e2):
          %Equal.sym(Nat, c, Nat.add(b, k2), e2) : {Nat.is_le(a, _) == True{} : Bool}
          %Equal.sym(Nat, b, Nat.add(a, k1), e1) : {Nat.is_le(a, Nat.add(_, k2)) == True{} : Bool}
          %Equal.sym(Nat, Nat.add(Nat.add(a, k1), k2), Nat.add(a, Nat.add(k1, k2)), P.add_assoc(a, k1, k2)) :
            {Nat.is_le(a, _) == True{} : Bool}
          P.le_of_add(a, Nat.add(k1, k2))

def le_trans(a, b, c, e1, e2):
  le_trans.k(a, b, c, P.le_witness(a, b, e1), P.le_witness(b, c, e2))

law add_cancel_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for e: {Nat.add(c, a) == Nat.add(c, b) : Nat}
  {a == b : Nat}

def add_cancel_l(c, a, b, e):
  match c:
    case 0n:
      e
    case 1n+k:
      add_cancel_l(k, a, b, P.succ_inj(Nat.add(k, a), Nat.add(k, b), e))

# ((a+b)+c) + ((a'+b')+c') regrouped as ((a+a')+(b+b')) + (c+c').
def swap3(+a: Nat, +b: Nat, +c: Nat, +a2: Nat, +b2: Nat, +c2: Nat) ->
  {Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a2, b2), c2))
    == Nat.add(Nat.add(Nat.add(a, a2), Nat.add(b, b2)), Nat.add(c, c2)) : Nat}:
  %P.add_swap(a, b, a2, b2) : {Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a2, b2), c2))
    == Nat.add(_, Nat.add(c, c2)) : Nat}
  P.add_swap(Nat.add(a, b), c, Nat.add(a2, b2), c2)

# Room for n mines and 9 more among the L + O cells, with O <= 9: n <= L.
def room_left.k(+l: Nat, +o: Nat, +m: Nat, +n: Nat, e: {Nat.add(l, o) == m : Nat},
  wb: P.LeW(o, 9n), wr: P.LeW(Nat.add(n, 9n), m)) -> {Nat.is_le(n, l) == True{} : Bool}:
  match wb:
    case (+d, eb):
      match wr:
        case (+k, er):
          +dk = Nat.add(d, k)
          +t1 = Equal.trans(Nat, Nat.add(o, l), m, Nat.add(Nat.add(n, 9n), k),
            Equal.trans(Nat, Nat.add(o, l), Nat.add(l, o), m, P.add_comm(o, l), e), er)
          +t2 = Equal.cong(Nat, Nat, x => Nat.add(Nat.add(n, x), k), 9n, Nat.add(o, d), eb)
          +t4 = Equal.cong(Nat, Nat, x => Nat.add(n, x), Nat.add(Nat.add(o, d), k), Nat.add(o, dk), P.add_assoc(o, d, k))
          +t345 = Equal.trans(Nat, Nat.add(Nat.add(n, Nat.add(o, d)), k), Nat.add(n, Nat.add(Nat.add(o, d), k)),
            Nat.add(o, Nat.add(n, dk)), P.add_assoc(n, Nat.add(o, d), k),
            Equal.trans(Nat, Nat.add(n, Nat.add(Nat.add(o, d), k)), Nat.add(n, Nat.add(o, dk)), Nat.add(o, Nat.add(n, dk)),
              t4, P.add_left_comm(n, o, dk)))
          +e3 = Equal.trans(Nat, Nat.add(o, l), Nat.add(Nat.add(n, 9n), k), Nat.add(o, Nat.add(n, dk)), t1,
            Equal.trans(Nat, Nat.add(Nat.add(n, 9n), k), Nat.add(Nat.add(n, Nat.add(o, d)), k), Nat.add(o, Nat.add(n, dk)),
              t2, t345))
          %Equal.sym(Nat, l, Nat.add(n, dk), add_cancel_l(o, l, Nat.add(n, dk), e3)) : {Nat.is_le(n, _) == True{} : Bool}
          P.le_of_add(n, dk)

def room_left(+l: Nat, +o: Nat, +m: Nat, +n: Nat, e: {Nat.add(l, o) == m : Nat},
  r: {Nat.is_le(Nat.add(n, 9n), m) == True{} : Bool}, b: {Nat.is_le(o, 9n) == True{} : Bool}) ->
  {Nat.is_le(n, l) == True{} : Bool}:
  room_left.k(l, o, m, n, e, P.le_witness(o, 9n, b), P.le_witness(Nat.add(n, 9n), m, r))

# At most nine cells near the first click
# =======================================

# x is within one step of a.
def nr(+a: Nat, +x: Nat) -> Bool:
  Nat.is_le(B.dist(a, x), 1n)

# How many elements of xs are within one step of a.
def ncnt(+a: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(one(nr(a, x)), ncnt(a, t))

# How many elements of xs are one below a.
def cnt1(+a: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(one(Nat.is_eq(1n+x, a)), cnt1(a, t))

# Within one step of a means a, a + 1 or a - 1.
law near_pt:
  for +a: Nat
  for +x: Nat
  {Nat.is_le(one(nr(a, x)), Nat.add(Nat.add(one(Nat.is_eq(x, a)), one(Nat.is_eq(x, 1n+a))), one(Nat.is_eq(1n+x, a))))
    == True{} : Bool}

def near_pt.zx(+j: Nat) ->
  {Nat.is_le(one(nr(0n, 1n+j)), Nat.add(Nat.add(one(Nat.is_eq(1n+j, 0n)), one(Nat.is_eq(1n+j, 1n))), one(Nat.is_eq(2n+j, 0n))))
    == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      P.le_zero_l(Nat.add(Nat.add(one(Nat.is_eq(2n+i, 0n)), one(Nat.is_eq(2n+i, 1n))), one(Nat.is_eq(3n+i, 0n))))

def near_pt.xz(+k: Nat) ->
  {Nat.is_le(one(nr(1n+k, 0n)), Nat.add(Nat.add(one(Nat.is_eq(0n, 1n+k)), one(Nat.is_eq(0n, 2n+k))), one(Nat.is_eq(1n, 1n+k))))
    == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+i:
      P.le_zero_l(Nat.add(Nat.add(one(Nat.is_eq(0n, 2n+i)), one(Nat.is_eq(0n, 3n+i))), one(Nat.is_eq(1n, 2n+i))))

def near_pt(a, x):
  match a x:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      near_pt.zx(j)
    case 1n+k 0n:
      near_pt.xz(k)
    case 1n+k 1n+j:
      near_pt(k, j)

law near_cnt:
  for +a: Nat
  for +xs: List<&2, Nat>
  {Nat.is_le(ncnt(a, xs), Nat.add(Nat.add(cnt(a, xs), cnt(1n+a, xs)), cnt1(a, xs))) == True{} : Bool}

def near_cnt(a, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      +o1 = one(Nat.is_eq(x, a))
      +o2 = one(Nat.is_eq(x, 1n+a))
      +o3 = one(Nat.is_eq(1n+x, a))
      %swap3(o1, o2, o3, cnt(a, t), cnt(1n+a, t), cnt1(a, t)) :
        {Nat.is_le(Nat.add(one(nr(a, x)), ncnt(a, t)), _) == True{} : Bool}
      P.le_add(one(nr(a, x)), Nat.add(Nat.add(o1, o2), o3), ncnt(a, t), Nat.add(Nat.add(cnt(a, t), cnt(1n+a, t)), cnt1(a, t)),
        near_pt(a, x), near_cnt(a, t))

law cnt1_succ:
  for +a: Nat
  for +xs: List<&2, Nat>
  {cnt1(1n+a, xs) == cnt(a, xs) : Nat}

def cnt1_succ(a, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %cnt1_succ(a, t) : {Nat.add(one(Nat.is_eq(1n+x, 1n+a)), cnt1(1n+a, t))
        == Nat.add(one(Nat.is_eq(x, a)), _) : Nat}
      {==}

law cnt1_zero:
  for +xs: List<&2, Nat>
  {cnt1(0n, xs) == 0n : Nat}

def cnt1_zero(xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      cnt1_zero(t)

def pick_le1(+b: Bool) -> {Nat.is_le(Bool.pick(Nat, b, 1n, 0n), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cnt_le1(+i: Nat, +n: Nat) -> {Nat.is_le(cnt(i, List.range(n)), 1n) == True{} : Bool}:
  %Equal.sym(Nat, cnt(i, List.range(n)), Bool.pick(Nat, Nat.is_lt(i, n), 1n, 0n), cnt_range(i, n)) :
    {Nat.is_le(_, 1n) == True{} : Bool}
  pick_le1(Nat.is_lt(i, n))

def cnt1_le1(+a: Nat, +n: Nat) -> {Nat.is_le(cnt1(a, List.range(n)), 1n) == True{} : Bool}:
  match a:
    case 0n:
      %Equal.sym(Nat, cnt1(0n, List.range(n)), 0n, cnt1_zero(List.range(n))) : {Nat.is_le(_, 1n) == True{} : Bool}
      {==}
    case 1n+k:
      %Equal.sym(Nat, cnt1(1n+k, List.range(n)), cnt(k, List.range(n)), cnt1_succ(k, List.range(n))) :
        {Nat.is_le(_, 1n) == True{} : Bool}
      cnt_le1(k, n)

# At most three numbers below n are within one step of a.
law ncnt_le3:
  for +a: Nat
  for +n: Nat
  {Nat.is_le(ncnt(a, List.range(n)), 3n) == True{} : Bool}

def ncnt_le3(a, n):
  +xs = List.range(n)
  le_trans(ncnt(a, xs), Nat.add(Nat.add(cnt(a, xs), cnt(1n+a, xs)), cnt1(a, xs)), 3n,
    near_cnt(a, xs),
    P.le_add(Nat.add(cnt(a, xs), cnt(1n+a, xs)), 2n, cnt1(a, xs), 1n,
      P.le_add(cnt(a, xs), 1n, cnt(1n+a, xs), 1n, cnt_le1(a, n), cnt_le1(1n+a, n)),
      cnt1_le1(a, n)))

def wide_row.go(+fx: Nat, +fy: Nat, +y: Nat, +xs: List<&2, Nat>, +b: Bool,
  +e: {nr(fy, y) == b : Bool}) ->
  {outs(G.Zone{T.Pos{fx, fy}, True{}}, B.row_cells(y, xs)) == Bool.pick(Nat, b, ncnt(fx, xs), 0n) : Nat}:
  match xs:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case x <> t:
      %Equal.sym(Bool, nr(fy, y), b, e) :
        {Nat.add(Bool.pick(Nat, Bool.and(nr(fx, x), _), 1n, 0n), outs(G.Zone{T.Pos{fx, fy}, True{}}, B.row_cells(y, t)))
          == Bool.pick(Nat, b, ncnt(fx, x <> t), 0n) : Nat}
      %Equal.sym(Nat, outs(G.Zone{T.Pos{fx, fy}, True{}}, B.row_cells(y, t)), Bool.pick(Nat, b, ncnt(fx, t), 0n),
        wide_row.go(fx, fy, y, t, b, e)) :
        {Nat.add(Bool.pick(Nat, Bool.and(nr(fx, x), b), 1n, 0n), _)
          == Bool.pick(Nat, b, ncnt(fx, x <> t), 0n) : Nat}
      firsts_row.end(nr(fx, x), b, ncnt(fx, t))

# Each row near the first click's row, counted c times.
def rsum(+fy: Nat, +c: Nat, ys: List<&2, Nat>) -> Nat:
  match ys:
    case Nil{}:
      0n
    case y <> t:
      Nat.add(Bool.pick(Nat, nr(fy, y), c, 0n), rsum(fy, c, t))

law wide_rows:
  for +fx: Nat
  for +fy: Nat
  for +w: Nat
  for +ys: List<&2, Nat>
  {outs(G.Zone{T.Pos{fx, fy}, True{}}, B.cells.go(w, ys)) == rsum(fy, ncnt(fx, List.range(w)), ys) : Nat}

def wide_rows(fx, fy, w, ys):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +z = {G.Zone{T.Pos{fx, fy}, True{}} : G.Zone}
      +row = B.row_cells(y, List.range(w))
      +c = ncnt(fx, List.range(w))
      %Equal.sym(Nat, outs(z, List.append(&2, T.Pos, row, B.cells.go(w, t))),
        Nat.add(outs(z, row), outs(z, B.cells.go(w, t))), firsts_append(z, row, B.cells.go(w, t))) :
        {_ == rsum(fy, c, y <> t) : Nat}
      %Equal.sym(Nat, outs(z, row), Bool.pick(Nat, nr(fy, y), c, 0n), wide_row.go(fx, fy, y, List.range(w), nr(fy, y), {==})) :
        {Nat.add(_, outs(z, B.cells.go(w, t))) == rsum(fy, c, y <> t) : Nat}
      %Equal.sym(Nat, outs(z, B.cells.go(w, t)), rsum(fy, c, t), wide_rows(fx, fy, w, t)) :
        {Nat.add(Bool.pick(Nat, nr(fy, y), c, 0n), _) == rsum(fy, c, y <> t) : Nat}
      {==}

def pick_le3(+b: Bool, +c: Nat, lc: {Nat.is_le(c, 3n) == True{} : Bool}) ->
  {Nat.is_le(Bool.pick(Nat, b, c, 0n), Nat.add(Nat.add(one(b), one(b)), one(b))) == True{} : Bool}:
  match b:
    case True{}:
      lc
    case False{}:
      {==}

law rsum_le:
  for +fy: Nat
  for +c: Nat
  for +ys: List<&2, Nat>
  for +lc: {Nat.is_le(c, 3n) == True{} : Bool}
  {Nat.is_le(rsum(fy, c, ys), Nat.add(Nat.add(ncnt(fy, ys), ncnt(fy, ys)), ncnt(fy, ys))) == True{} : Bool}

def rsum_le(fy, c, ys, lc):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +o = one(nr(fy, y))
      +nt = ncnt(fy, t)
      %swap3(o, o, o, nt, nt, nt) :
        {Nat.is_le(rsum(fy, c, y <> t), _) == True{} : Bool}
      P.le_add(Bool.pick(Nat, nr(fy, y), c, 0n), Nat.add(Nat.add(o, o), o), rsum(fy, c, t), Nat.add(Nat.add(nt, nt), nt),
        pick_le3(nr(fy, y), c, lc), rsum_le(fy, c, t, lc))

# The zone around a first click holds at most 9 cells of the board.
law wide_le9:
  for +fx: Nat
  for +fy: Nat
  for +w: Nat
  for +h: Nat
  {Nat.is_le(outs(G.Zone{T.Pos{fx, fy}, True{}}, B.cells(w, h)), 9n) == True{} : Bool}

def wide_le9(fx, fy, w, h):
  +c = ncnt(fx, List.range(w))
  +ny = ncnt(fy, List.range(h))
  %Equal.sym(Nat, outs(G.Zone{T.Pos{fx, fy}, True{}}, B.cells(w, h)), rsum(fy, c, List.range(h)),
    wide_rows(fx, fy, w, List.range(h))) : {Nat.is_le(_, 9n) == True{} : Bool}
  le_trans(rsum(fy, c, List.range(h)), Nat.add(Nat.add(ny, ny), ny), 9n,
    rsum_le(fy, c, List.range(h), ncnt_le3(fx, w)),
    P.le_add(Nat.add(ny, ny), 6n, ny, 3n,
      P.le_add(ny, 3n, ny, 3n, ncnt_le3(fy, h), ncnt_le3(fy, h)), ncnt_le3(fy, h)))

# Exactly n mines, again
# =====================

def cells_len(+w: Nat, +h: Nat) -> {List.length(&2, T.Pos, B.cells(w, h)) == Nat.mul(w, h) : Nat}:
  Equal.trans(Nat, List.length(&2, T.Pos, B.cells(w, h)),
    Nat.mul(List.length(&2, Nat, List.range(h)), w), Nat.mul(w, h),
    cells_go_len(w, List.range(h)),
    %Equal.sym(Nat, List.length(&2, Nat, List.range(h)), h, P.range_length(h)) :
      {Nat.mul(_, w) == Nat.mul(w, h) : Nat};
      P.mul_comm(h, w))

# With just the first click kept free, there are w*h - 1 candidates, so
# n < w*h mines fit among them.
law gen_inv_one:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +fx: Nat
  for +fy: Nat
  for +on: {L.on_board(w, h, T.Pos{fx, fy}) == True{} : Bool}
  for fits: {Nat.is_lt(n, Nat.mul(w, h)) == True{} : Bool}
  {Nat.is_le(n, G.gen.left(G.Zone{T.Pos{fx, fy}, False{}}, B.cells(w, h))) == True{} : Bool}

def gen_inv_one(w, h, n, fx, fy, on, fits):
  +z = {G.Zone{T.Pos{fx, fy}, False{}} : G.Zone}
  +gl = G.gen.left(z, B.cells(w, h))
  +xw = P.and_true_l(Nat.is_lt(fx, w), Nat.is_lt(fy, h), on)
  +yh = P.and_true_r(Nat.is_lt(fx, w), Nat.is_lt(fy, h), on)
  +f1 = Equal.trans(Nat, outs(z, B.cells(w, h)), cnt(fy, List.range(h)), 1n,
    firsts_rows(fx, fy, w, List.range(h), one_when(fx, w, xw)), one_when(fy, h, yh))
  +e1 = {%f1 : {Nat.add(gl, _) == List.length(&2, T.Pos, B.cells(w, h)) : Nat};
    gen_left_firsts(z, B.cells(w, h)) : {Nat.add(gl, 1n) == List.length(&2, T.Pos, B.cells(w, h)) : Nat}}
  +e2 = Equal.trans(Nat, 1n+gl, Nat.add(gl, 1n), Nat.mul(w, h),
    Equal.sym(Nat, Nat.add(gl, 1n), 1n+gl, P.add_one(gl)),
    Equal.trans(Nat, Nat.add(gl, 1n), List.length(&2, T.Pos, B.cells(w, h)), Nat.mul(w, h), e1, cells_len(w, h)))
  P.lt_succ_le(n, gl,
    {%Equal.sym(Nat, 1n+gl, Nat.mul(w, h), e2) : {Nat.is_lt(n, _) == True{} : Bool};
      fits : {Nat.is_lt(n, 1n+gl) == True{} : Bool}})

# With room for 9 more, n mines fit outside the wider zone.
law gen_inv_wide:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +fx: Nat
  for +fy: Nat
  for room: {Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h)) == True{} : Bool}
  {Nat.is_le(n, G.gen.left(G.Zone{T.Pos{fx, fy}, True{}}, B.cells(w, h))) == True{} : Bool}

def gen_inv_wide(w, h, n, fx, fy, room):
  +z = {G.Zone{T.Pos{fx, fy}, True{}} : G.Zone}
  +gl = G.gen.left(z, B.cells(w, h))
  +o = outs(z, B.cells(w, h))
  room_left(gl, o, Nat.mul(w, h), n,
    Equal.trans(Nat, Nat.add(gl, o), List.length(&2, T.Pos, B.cells(w, h)), Nat.mul(w, h),
      gen_left_firsts(z, B.cells(w, h)), cells_len(w, h)),
    room, wide_le9(fx, fy, w, h))

def gen_inv.k(+w: Nat, +h: Nat, +n: Nat, +fx: Nat, +fy: Nat,
  +on: {L.on_board(w, h, T.Pos{fx, fy}) == True{} : Bool}, fits: {Nat.is_lt(n, Nat.mul(w, h)) == True{} : Bool},
  +wide: Bool, ew: {Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h)) == wide : Bool}) ->
  {Nat.is_le(n, G.gen.left(G.Zone{T.Pos{fx, fy}, wide}, B.cells(w, h))) == True{} : Bool}:
  match wide:
    case False{}:
      gen_inv_one(w, h, n, fx, fy, on, fits)
    case True{}:
      gen_inv_wide(w, h, n, fx, fy, ew)

# Whichever zone the board keeps free, the n mines fit outside it.
law gen_inv:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +first: T.Pos
  for +on: {L.on_board(w, h, first) == True{} : Bool}
  for fits: {Nat.is_lt(n, Nat.mul(w, h)) == True{} : Bool}
  {Nat.is_le(n, G.gen.left(zone(w, h, n, first), B.cells(w, h))) == True{} : Bool}

def gen_inv(w, h, n, first, on, fits):
  match first:
    case T.Pos{fx, fy}:
      gen_inv.k(w, h, n, fx, fy, on, fits, Nat.is_le(Nat.add(n, 9n), Nat.mul(w, h)), {==})

law gen_count_:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +first: T.Pos
  for +rs: List<&2, U32>
  for on: {L.on_board(w, h, first) == True{} : Bool}
  for fits: {Nat.is_lt(n, Nat.mul(w, h)) == True{} : Bool}
  {L.total_mines(G.place_mines(w, h, n, first, rs)) == n : Nat}

def gen_count_(w, h, n, first, rs, on, fits):
  +z = zone(w, h, n, first)
  gen_rows_count(z, w, List.range(h),
    {G.GenState{n, G.gen.left(z, B.cells(w, h)), rs} : G.GenState},
    gen_inv(w, h, n, first, on, fits), {==})
