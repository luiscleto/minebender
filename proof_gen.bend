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
  for +first: T.Pos
  for +y: Nat
  for +xs: List<&2, Nat>
  for +st: G.GenState
  {List.length(&2, Bool, G.gen.row(first, y, xs, st)) == List.length(&2, Nat, xs) : Nat}

def gen_row_len(first, y, xs, st):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %gen_row_len(first, y, t, G.gen.next(first, T.Pos{x, y}, st)) :
        {1n+List.length(&2, Bool, G.gen.row(first, y, t, G.gen.next(first, T.Pos{x, y}, st)))
          == 1n+_ : Nat}
      {==}

law gen_rows_len:
  for +first: T.Pos
  for +w: Nat
  for +ys: List<&2, Nat>
  for +st: G.GenState
  {List.length(&2, List<&2, Bool>, G.gen.rows(first, w, ys, st)) == List.length(&2, Nat, ys) : Nat}

def gen_rows_len(first, w, ys, st):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +st2 = G.gen.row_state(first, y, List.range(w), st)
      %gen_rows_len(first, w, t, st2) :
        {1n+List.length(&2, List<&2, Bool>, G.gen.rows(first, w, t, st2)) == 1n+_ : Nat}
      {==}

law gen_rows_wide:
  for +first: T.Pos
  for +w: Nat
  for +ys: List<&2, Nat>
  for +st: G.GenState
  {L.rows_wide(Bool, w, G.gen.rows(first, w, ys, st)) == True{} : Bool}

def gen_rows_wide(first, w, ys, st):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +row = G.gen.row(first, y, List.range(w), st)
      +st2 = G.gen.row_state(first, y, List.range(w), st)
      +len = Equal.trans(Nat, List.length(&2, Bool, row), List.length(&2, Nat, List.range(w)), w,
        gen_row_len(first, y, List.range(w), st), P.range_length(w))
      %Equal.sym(Nat, List.length(&2, Bool, row), w, len) :
        {Bool.and(Nat.is_eq(_, w), L.rows_wide(Bool, w, G.gen.rows(first, w, t, st2))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(w, w), True{}, P.eq_refl(w)) :
        {Bool.and(_, L.rows_wide(Bool, w, G.gen.rows(first, w, t, st2))) == True{} : Bool}
      gen_rows_wide(first, w, t, st2)

law gen_shape_:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +first: T.Pos
  for +rs: List<&2, U32>
  {L.shaped(Bool, w, h, G.place_mines(w, h, n, first, rs)) == True{} : Bool}

def gen_shape_(w, h, n, first, rs):
  +st = {G.GenState{n, G.gen.left(first, B.cells(w, h)), rs} : G.GenState}
  +g = G.gen.rows(first, w, List.range(h), st)
  +len = Equal.trans(Nat, List.length(&2, List<&2, Bool>, g), List.length(&2, Nat, List.range(h)), h,
    gen_rows_len(first, w, List.range(h), st), P.range_length(h))
  %Equal.sym(Nat, List.length(&2, List<&2, Bool>, g), h, len) :
    {Bool.and(Nat.is_eq(_, h), L.rows_wide(Bool, w, g)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(h, h), True{}, P.eq_refl(h)) :
    {Bool.and(_, L.rows_wide(Bool, w, g)) == True{} : Bool}
  gen_rows_wide(first, w, List.range(h), st)

# The first click
# ===============

def gen_bit_first(+first: T.Pos, +p: T.Pos, +st: G.GenState,
  s: {B.same(p, first) == True{} : Bool}) -> {G.gen.bit(first, p, st) == False{} : Bool}:
  match st:
    case G.GenState{need, left, rs}:
      %Equal.sym(Bool, B.same(p, first), True{}, s) :
        {Bool.and(Bool.and(Bool.not(_), Nat.is_lt(0n, need)), G.gen.pick(need, left, rs))
          == False{} : Bool}
      {==}

# A cell of a generated row that is the first click has no mine.
law gen_row_first:
  for +first: T.Pos
  for +y: Nat
  for +xs: List<&2, Nat>
  for +j: Nat
  for +x: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, xs, j) == Some{x} : Maybe<&2, Nat>}
  for +s: {B.same(T.Pos{x, y}, first) == True{} : Bool}
  {List.get(&2, Bool, G.gen.row(first, y, xs, st), j) == Some{False{}} : Maybe<&2, Bool>}

def gen_row_first(first, y, xs, j, x, st, e, s):
  match xs j:
    case Nil{} _:
      Empty.absurd({List.get(&2, Bool, G.gen.row(first, y, Nil{}, st), j) == Some{False{}}
        : Maybe<&2, Bool>}, PG.know_row_get.none(Nat, x, e))
    case a <> t 0n:
      %Equal.sym(Nat, a, x, PG.know_row_get.some(Nat, a, x, e)) :
        {Some{G.gen.bit(first, T.Pos{_, y}, st)} == Some{False{}} : Maybe<&2, Bool>}
      %Equal.sym(Bool, G.gen.bit(first, T.Pos{x, y}, st), False{},
        gen_bit_first(first, T.Pos{x, y}, st, s)) :
        {Some{_} == Some{False{}} : Maybe<&2, Bool>}
      {==}
    case a <> t 1n+k:
      gen_row_first(first, y, t, k, x, G.gen.next(first, T.Pos{a, y}, st), e, s)

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
  for +first: T.Pos
  for +y: Nat
  for +xs: List<&2, Nat>
  for +j: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, xs, j) == None{} : Maybe<&2, Nat>}
  {List.get(&2, Bool, G.gen.row(first, y, xs, st), j) == None{} : Maybe<&2, Bool>}

def gen_row_out(first, y, xs, j, st, e):
  match xs j:
    case Nil{} _:
      {==}
    case a <> t 0n:
      Empty.absurd({List.get(&2, Bool, G.gen.row(first, y, a <> t, st), 0n) == None{}
        : Maybe<&2, Bool>}, gen_some_ne_none(Nat, a, e))
    case a <> t 1n+k:
      gen_row_out(first, y, t, k, G.gen.next(first, T.Pos{a, y}, st), e)

law gen_rows_get:
  for +first: T.Pos
  for +w: Nat
  for +ys: List<&2, Nat>
  for +i: Nat
  for +y: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, ys, i) == Some{y} : Maybe<&2, Nat>}
  exs st2: G.GenState
  {List.get(&2, List<&2, Bool>, G.gen.rows(first, w, ys, st), i)
    == Some{G.gen.row(first, y, List.range(w), st2)} : Maybe<&2, List<&2, Bool>>}

def gen_rows_get(first, w, ys, i, y, st, e):
  match ys i:
    case Nil{} _:
      Empty.absurd(Exists(G.GenState, st2 => {List.get(&2, List<&2, Bool>,
        G.gen.rows(first, w, Nil{}, st), i) == Some{G.gen.row(first, y, List.range(w), st2)}
        : Maybe<&2, List<&2, Bool>>}), PG.know_row_get.none(Nat, y, e))
    case a <> t 0n:
      %PG.know_row_get.some(Nat, a, y, e) :
        Exists(G.GenState, st2 => {Some{G.gen.row(first, a, List.range(w), st)}
          == Some{G.gen.row(first, _, List.range(w), st2)} : Maybe<&2, List<&2, Bool>>})
      (st, {==})
    case a <> t 1n+k:
      gen_rows_get(first, w, t, k, y, G.gen.row_state(first, a, List.range(w), st), e)

law gen_rows_out:
  for +first: T.Pos
  for +w: Nat
  for +ys: List<&2, Nat>
  for +i: Nat
  for +st: G.GenState
  for e: {List.get(&2, Nat, ys, i) == None{} : Maybe<&2, Nat>}
  {List.get(&2, List<&2, Bool>, G.gen.rows(first, w, ys, st), i) == None{}
    : Maybe<&2, List<&2, Bool>>}

def gen_rows_out(first, w, ys, i, st, e):
  match ys i:
    case Nil{} _:
      {==}
    case a <> t 0n:
      Empty.absurd({List.get(&2, List<&2, Bool>, G.gen.rows(first, w, a <> t, st), 0n) == None{}
        : Maybe<&2, List<&2, Bool>>}, gen_some_ne_none(Nat, a, e))
    case a <> t 1n+k:
      gen_rows_out(first, w, t, k, G.gen.row_state(first, a, List.range(w), st), e)

def gen_first.col(+first: T.Pos, +fx: Nat, +fy: Nat, +w: Nat, +st2: G.GenState,
  s: {B.same(T.Pos{fx, fy}, first) == True{} : Bool}, +b: Bool,
  e: {Nat.is_lt(fx, w) == b : Bool}) ->
  {Maybe.default(&2, Bool, List.get(&2, Bool, G.gen.row(first, fy, List.range(w), st2), fx), False{})
    == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Bool>, List.get(&2, Bool, G.gen.row(first, fy, List.range(w), st2), fx),
        Some{False{}},
        gen_row_first(first, fy, List.range(w), fx, fx, st2, P.range_get(w, fx, e), s)) :
        {Maybe.default(&2, Bool, _, False{}) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Bool>, List.get(&2, Bool, G.gen.row(first, fy, List.range(w), st2), fx),
        None{}, gen_row_out(first, fy, List.range(w), fx, st2, P.range_get_out(w, fx, e))) :
        {Maybe.default(&2, Bool, _, False{}) == False{} : Bool}
      {==}

def gen_first.found(+first: T.Pos, +fx: Nat, +fy: Nat, +w: Nat, +g: T.Grid(Bool),
  s: {B.same(T.Pos{fx, fy}, first) == True{} : Bool},
  r: Exists(G.GenState, st2 => {List.get(&2, List<&2, Bool>, g, fy)
    == Some{G.gen.row(first, fy, List.range(w), st2)} : Maybe<&2, List<&2, Bool>>})) ->
  {L.mine(g, T.Pos{fx, fy}) == False{} : Bool}:
  match r:
    case (st2, eq):
      %Equal.sym(Maybe<&2, List<&2, Bool>>, List.get(&2, List<&2, Bool>, g, fy),
        Some{G.gen.row(first, fy, List.range(w), st2)}, eq) :
        {Maybe.default(&2, Bool, List.get(&2, Bool,
          Maybe.default(&2, List<&2, Bool>, _, Nil{}), fx), False{}) == False{} : Bool}
      gen_first.col(first, fx, fy, w, st2, s, Nat.is_lt(fx, w), {==})

def gen_first.row(+first: T.Pos, +fx: Nat, +fy: Nat, +w: Nat, +h: Nat, +st: G.GenState,
  s: {B.same(T.Pos{fx, fy}, first) == True{} : Bool}, +b: Bool,
  e: {Nat.is_lt(fy, h) == b : Bool}) ->
  {L.mine(G.gen.rows(first, w, List.range(h), st), T.Pos{fx, fy}) == False{} : Bool}:
  match b:
    case True{}:
      gen_first.found(first, fx, fy, w, G.gen.rows(first, w, List.range(h), st), s,
        gen_rows_get(first, w, List.range(h), fy, fy, st, P.range_get(h, fy, e)))
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, Bool>>,
        List.get(&2, List<&2, Bool>, G.gen.rows(first, w, List.range(h), st), fy), None{},
        gen_rows_out(first, w, List.range(h), fy, st, P.range_get_out(h, fy, e))) :
        {Maybe.default(&2, Bool, List.get(&2, Bool,
          Maybe.default(&2, List<&2, Bool>, _, Nil{}), fx), False{}) == False{} : Bool}
      {==}

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
      gen_first.row(p, fx, fy, w, h,
        {G.GenState{n, G.gen.left(p, B.cells(w, h)), rs} : G.GenState},
        PG.same_refl(p), Nat.is_lt(fy, h), {==})

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
# every cell other than the first click.
def GenStep(+first: T.Pos, +p: T.Pos, +st: G.GenState, +lp: Nat) -> Type:
  {Nat.add(one(G.gen.bit(first, p, st)), st_need(G.gen.next(first, p, st))) == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.next(first, p, st)), st_left(G.gen.next(first, p, st))) == True{} : Bool} &
  {st_left(G.gen.next(first, p, st)) == lp : Nat}

def gen_pick_false(+need: Nat, +left: Nat, +rs: List<&2, U32>,
  e: {G.gen.pick(need, left, rs) == False{} : Bool}) -> {Nat.is_eq(need, left) == False{} : Bool}:
  match rs:
    case Nil{}:
      e
    case r <> t:
      P.or_false_inv(Nat.is_eq(need, left), G.gen.coin(r, left, need), e)

def gen_take(+first: T.Pos, +p: T.Pos, +m: Nat, +lp: Nat, +rs: List<&2, U32>,
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

def gen_cell.need(+first: T.Pos, +p: T.Pos, +need: Nat, +lp: Nat, +rs: List<&2, U32>,
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
      gen_take(first, p, m, lp, rs, inv, G.gen.pick(1n+m, 1n+lp, rs), {==})

def gen_cell.go(+first: T.Pos, +p: T.Pos, +need: Nat, +left: Nat, +rs: List<&2, U32>, +lp: Nat,
  inv: {Nat.is_le(need, left) == True{} : Bool}, +s: Bool, e: {B.same(p, first) == s : Bool},
  +lft: {left == Nat.add(Bool.pick(Nat, s, 0n, 1n), lp) : Nat}) ->
  GenStep(first, p, G.GenState{need, left, rs}, lp):
  match s:
    case True{}:
      %Equal.sym(Bool, B.same(p, first), True{}, e) :
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
      %Equal.sym(Bool, B.same(p, first), False{}, e) :
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
      gen_cell.need(first, p, need, lp, rs,
        {%lft : {Nat.is_le(need, _) == True{} : Bool}; inv : {Nat.is_le(need, 1n+lp) == True{} : Bool}})


law gen_cell:
  for +first: T.Pos
  for +p: T.Pos
  for +st: G.GenState
  for +lp: Nat
  for inv: {Nat.is_le(st_need(st), st_left(st)) == True{} : Bool}
  for lft: {st_left(st) == Nat.add(Bool.pick(Nat, B.same(p, first), 0n, 1n), lp) : Nat}
  GenStep(first, p, st, lp)

def gen_cell(first, p, st, lp, inv, lft):
  match st:
    case G.GenState{need, left, rs}:
      gen_cell.go(first, p, need, left, rs, lp, inv, B.same(p, first), {==}, lft)

def gen_row_count.step(+first: T.Pos, +p: T.Pos, +st: G.GenState, +rm: Nat, +nf: Nat,
  s1: {Nat.add(one(G.gen.bit(first, p, st)), st_need(G.gen.next(first, p, st))) == st_need(st) : Nat},
  r1: {Nat.add(rm, nf) == st_need(G.gen.next(first, p, st)) : Nat}) ->
  {Nat.add(Nat.add(one(G.gen.bit(first, p, st)), rm), nf) == st_need(st) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(one(G.gen.bit(first, p, st)), rm), nf),
    Nat.add(one(G.gen.bit(first, p, st)), Nat.add(rm, nf)),
    P.add_assoc(one(G.gen.bit(first, p, st)), rm, nf)) : {_ == st_need(st) : Nat}
  %Equal.sym(Nat, Nat.add(rm, nf), st_need(G.gen.next(first, p, st)), r1) :
    {Nat.add(one(G.gen.bit(first, p, st)), _) == st_need(st) : Nat}
  s1

def gen_row_count.k2(+first: T.Pos, +y: Nat, +t: List<&2, Nat>, +p: T.Pos, +st: G.GenState,
  +cs: List<&2, T.Pos>,
  s1: {Nat.add(one(G.gen.bit(first, p, st)), st_need(G.gen.next(first, p, st))) == st_need(st) : Nat},
  r: {Nat.add(L.row_mines(G.gen.row(first, y, t, G.gen.next(first, p, st))),
       st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == st_need(G.gen.next(first, p, st)) : Nat} &
    {Nat.is_le(st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st))),
       st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == True{} : Bool} &
    {st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st))) == G.gen.left(first, cs) : Nat}) ->
  {Nat.add(Nat.add(one(G.gen.bit(first, p, st)), L.row_mines(G.gen.row(first, y, t, G.gen.next(first, p, st)))),
     st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st))),
     st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == True{} : Bool} &
  {st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st))) == G.gen.left(first, cs) : Nat}:
  match r:
    case (r1, rest):
      (gen_row_count.step(first, p, st,
        L.row_mines(G.gen.row(first, y, t, G.gen.next(first, p, st))),
        st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st))), s1, r1), rest)

def gen_row_count.k(+first: T.Pos, +y: Nat, +t: List<&2, Nat>, +p: T.Pos, +st: G.GenState,
  +cs: List<&2, T.Pos>,
  step: GenStep(first, p, st, G.gen.left(first, List.append(&2, T.Pos, B.row_cells(y, t), cs))),
  ih: ({Nat.is_le(st_need(G.gen.next(first, p, st)), st_left(G.gen.next(first, p, st))) == True{} : Bool} ->
    {st_left(G.gen.next(first, p, st)) == G.gen.left(first, List.append(&2, T.Pos, B.row_cells(y, t), cs)) : Nat} ->
    {Nat.add(L.row_mines(G.gen.row(first, y, t, G.gen.next(first, p, st))),
       st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == st_need(G.gen.next(first, p, st)) : Nat} &
    {Nat.is_le(st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st))),
       st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == True{} : Bool} &
    {st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st))) == G.gen.left(first, cs) : Nat})) ->
  {Nat.add(Nat.add(one(G.gen.bit(first, p, st)), L.row_mines(G.gen.row(first, y, t, G.gen.next(first, p, st)))),
     st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.row_state(first, y, t, G.gen.next(first, p, st))),
     st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st)))) == True{} : Bool} &
  {st_left(G.gen.row_state(first, y, t, G.gen.next(first, p, st))) == G.gen.left(first, cs) : Nat}:
  match step:
    case (s1, rest):
      match rest:
        case (s2, s3):
          gen_row_count.k2(first, y, t, p, st, cs, s1, ih(s2, s3))


law gen_row_count:
  for +first: T.Pos
  for +y: Nat
  for +xs: List<&2, Nat>
  for +st: G.GenState
  for +cs: List<&2, T.Pos>
  for inv: {Nat.is_le(st_need(st), st_left(st)) == True{} : Bool}
  for lft: {st_left(st) == G.gen.left(first, List.append(&2, T.Pos, B.row_cells(y, xs), cs)) : Nat}
  {Nat.add(L.row_mines(G.gen.row(first, y, xs, st)), st_need(G.gen.row_state(first, y, xs, st)))
    == st_need(st) : Nat} &
  {Nat.is_le(st_need(G.gen.row_state(first, y, xs, st)), st_left(G.gen.row_state(first, y, xs, st)))
    == True{} : Bool} &
  {st_left(G.gen.row_state(first, y, xs, st)) == G.gen.left(first, cs) : Nat}

def gen_row_count(first, y, xs, st, cs, inv, lft):
  match xs:
    case Nil{}:
      ({==}, (inv, lft))
    case x <> t:
      +p = {T.Pos{x, y} : T.Pos}
      +lp = G.gen.left(first, List.append(&2, T.Pos, B.row_cells(y, t), cs))
      +nx = G.gen.next(first, p, st)
      gen_row_count.k(first, y, t, p, st, cs, gen_cell(first, p, st, lp, inv, lft),
        s => gen_row_count(first, y, t, nx, cs, s))


def gen_rows_count.k(+first: T.Pos, +w: Nat, +y: Nat, +t: List<&2, Nat>, +st: G.GenState,
  r: {Nat.add(L.row_mines(G.gen.row(first, y, List.range(w), st)),
       st_need(G.gen.row_state(first, y, List.range(w), st))) == st_need(st) : Nat} &
    {Nat.is_le(st_need(G.gen.row_state(first, y, List.range(w), st)),
       st_left(G.gen.row_state(first, y, List.range(w), st))) == True{} : Bool} &
    {st_left(G.gen.row_state(first, y, List.range(w), st)) == G.gen.left(first, B.cells.go(w, t)) : Nat},
  ih: {Nat.is_le(st_need(G.gen.row_state(first, y, List.range(w), st)),
       st_left(G.gen.row_state(first, y, List.range(w), st))) == True{} : Bool} ->
    {st_left(G.gen.row_state(first, y, List.range(w), st)) == G.gen.left(first, B.cells.go(w, t)) : Nat} ->
    {L.total_mines(G.gen.rows(first, w, t, G.gen.row_state(first, y, List.range(w), st)))
      == st_need(G.gen.row_state(first, y, List.range(w), st)) : Nat}) ->
  {Nat.add(L.row_mines(G.gen.row(first, y, List.range(w), st)),
     L.total_mines(G.gen.rows(first, w, t, G.gen.row_state(first, y, List.range(w), st))))
    == st_need(st) : Nat}:
  match r:
    case (r1, rest):
      match rest:
        case (r2, r3):
          %Equal.sym(Nat, L.total_mines(G.gen.rows(first, w, t, G.gen.row_state(first, y, List.range(w), st))),
            st_need(G.gen.row_state(first, y, List.range(w), st)), ih(r2, r3)) :
            {Nat.add(L.row_mines(G.gen.row(first, y, List.range(w), st)), _) == st_need(st) : Nat}
          r1

law gen_rows_count:
  for +first: T.Pos
  for +w: Nat
  for +ys: List<&2, Nat>
  for +st: G.GenState
  for inv: {Nat.is_le(st_need(st), st_left(st)) == True{} : Bool}
  for lft: {st_left(st) == G.gen.left(first, B.cells.go(w, ys)) : Nat}
  {L.total_mines(G.gen.rows(first, w, ys, st)) == st_need(st) : Nat}

def gen_rows_count(first, w, ys, st, inv, lft):
  match ys:
    case Nil{}:
      Equal.sym(Nat, st_need(st), 0n, P.le_zero(st_need(st),
        {%lft : {Nat.is_le(st_need(st), _) == True{} : Bool};
          inv : {Nat.is_le(st_need(st), 0n) == True{} : Bool}}))
    case y <> t:
      +rs2 = G.gen.row_state(first, y, List.range(w), st)
      gen_rows_count.k(first, w, y, t, st,
        gen_row_count(first, y, List.range(w), st, B.cells.go(w, t), inv, lft),
        a => b => gen_rows_count(first, w, t, rs2, a, b))

# Counting the candidates
# =======================

# How many cells of ps are `first`.
def firsts(+first: T.Pos, ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> t:
      Nat.add(Bool.pick(Nat, B.same(p, first), 1n, 0n), firsts(first, t))

def gen_left_firsts.go(+first: T.Pos, +p: T.Pos, +t: List<&2, T.Pos>, +s: Bool,
  ih: {Nat.add(G.gen.left(first, t), firsts(first, t)) == List.length(&2, T.Pos, t) : Nat}) ->
  {Nat.add(Nat.add(Bool.pick(Nat, s, 0n, 1n), G.gen.left(first, t)),
     Nat.add(Bool.pick(Nat, s, 1n, 0n), firsts(first, t))) == 1n+List.length(&2, T.Pos, t) : Nat}:
  match s:
    case True{}:
      %Equal.sym(Nat, Nat.add(G.gen.left(first, t), 1n+firsts(first, t)),
        1n+Nat.add(G.gen.left(first, t), firsts(first, t)),
        P.add_succ(G.gen.left(first, t), firsts(first, t))) :
        {_ == 1n+List.length(&2, T.Pos, t) : Nat}
      %Equal.sym(Nat, Nat.add(G.gen.left(first, t), firsts(first, t)), List.length(&2, T.Pos, t), ih) :
        {1n+_ == 1n+List.length(&2, T.Pos, t) : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.add(G.gen.left(first, t), firsts(first, t)), List.length(&2, T.Pos, t), ih) :
        {1n+_ == 1n+List.length(&2, T.Pos, t) : Nat}
      {==}

# Every cell is either a candidate or the first click.
law gen_left_firsts:
  for +first: T.Pos
  for +ps: List<&2, T.Pos>
  {Nat.add(G.gen.left(first, ps), firsts(first, ps)) == List.length(&2, T.Pos, ps) : Nat}

def gen_left_firsts(first, ps):
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      gen_left_firsts.go(first, p, t, B.same(p, first), gen_left_firsts(first, t))

law firsts_append:
  for +first: T.Pos
  for +xs: List<&2, T.Pos>
  for +ys: List<&2, T.Pos>
  {firsts(first, List.append(&2, T.Pos, xs, ys)) == Nat.add(firsts(first, xs), firsts(first, ys)) : Nat}

def firsts_append(first, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case p <> t:
      %Equal.sym(Nat, firsts(first, List.append(&2, T.Pos, t, ys)),
        Nat.add(firsts(first, t), firsts(first, ys)), firsts_append(first, t, ys)) :
        {Nat.add(Bool.pick(Nat, B.same(p, first), 1n, 0n), _)
          == Nat.add(Nat.add(Bool.pick(Nat, B.same(p, first), 1n, 0n), firsts(first, t)), firsts(first, ys)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(Bool.pick(Nat, B.same(p, first), 1n, 0n), firsts(first, t)), firsts(first, ys)),
        Nat.add(Bool.pick(Nat, B.same(p, first), 1n, 0n), Nat.add(firsts(first, t), firsts(first, ys))),
        P.add_assoc(Bool.pick(Nat, B.same(p, first), 1n, 0n), firsts(first, t), firsts(first, ys)))

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
  {firsts(T.Pos{fx, fy}, B.row_cells(y, xs)) == Bool.pick(Nat, b, cnt(fx, xs), 0n) : Nat}:
  match xs:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case x <> t:
      %Equal.sym(Bool, Nat.is_eq(y, fy), b, e) :
        {Nat.add(Bool.pick(Nat, Bool.and(Nat.is_eq(x, fx), _), 1n, 0n), firsts(T.Pos{fx, fy}, B.row_cells(y, t)))
          == Bool.pick(Nat, b, cnt(fx, x <> t), 0n) : Nat}
      %Equal.sym(Nat, firsts(T.Pos{fx, fy}, B.row_cells(y, t)), Bool.pick(Nat, b, cnt(fx, t), 0n),
        firsts_row.go(fx, fy, y, t, b, e)) :
        {Nat.add(Bool.pick(Nat, Bool.and(Nat.is_eq(x, fx), b), 1n, 0n), _)
          == Bool.pick(Nat, b, cnt(fx, x <> t), 0n) : Nat}
      firsts_row.end(Nat.is_eq(x, fx), b, cnt(fx, t))

def firsts_rows.go(+fx: Nat, +fy: Nat, +w: Nat, +y: Nat, +t: List<&2, Nat>,
  c1: {cnt(fx, List.range(w)) == 1n : Nat},
  ih: {firsts(T.Pos{fx, fy}, B.cells.go(w, t)) == cnt(fy, t) : Nat}) ->
  {firsts(T.Pos{fx, fy}, List.append(&2, T.Pos, B.row_cells(y, List.range(w)), B.cells.go(w, t)))
    == cnt(fy, y <> t) : Nat}:
  +row = B.row_cells(y, List.range(w))
  %Equal.sym(Nat, firsts(T.Pos{fx, fy}, List.append(&2, T.Pos, row, B.cells.go(w, t))),
    Nat.add(firsts(T.Pos{fx, fy}, row), firsts(T.Pos{fx, fy}, B.cells.go(w, t))),
    firsts_append(T.Pos{fx, fy}, row, B.cells.go(w, t))) : {_ == cnt(fy, y <> t) : Nat}
  %Equal.sym(Nat, firsts(T.Pos{fx, fy}, row), Bool.pick(Nat, Nat.is_eq(y, fy), cnt(fx, List.range(w)), 0n),
    firsts_row.go(fx, fy, y, List.range(w), Nat.is_eq(y, fy), {==})) :
    {Nat.add(_, firsts(T.Pos{fx, fy}, B.cells.go(w, t))) == cnt(fy, y <> t) : Nat}
  %Equal.sym(Nat, cnt(fx, List.range(w)), 1n, c1) :
    {Nat.add(Bool.pick(Nat, Nat.is_eq(y, fy), _, 0n), firsts(T.Pos{fx, fy}, B.cells.go(w, t)))
      == cnt(fy, y <> t) : Nat}
  %Equal.sym(Nat, firsts(T.Pos{fx, fy}, B.cells.go(w, t)), cnt(fy, t), ih) :
    {Nat.add(Bool.pick(Nat, Nat.is_eq(y, fy), 1n, 0n), _) == cnt(fy, y <> t) : Nat}
  {==}

law firsts_rows:
  for +fx: Nat
  for +fy: Nat
  for +w: Nat
  for +ys: List<&2, Nat>
  for +c1: {cnt(fx, List.range(w)) == 1n : Nat}
  {firsts(T.Pos{fx, fy}, B.cells.go(w, ys)) == cnt(fy, ys) : Nat}

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

# On a board where the first click fits, there are w*h - 1 candidates, so
# n < w*h mines fit among them.
law gen_inv:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +first: T.Pos
  for +on: {L.on_board(w, h, first) == True{} : Bool}
  for fits: {Nat.is_lt(n, Nat.mul(w, h)) == True{} : Bool}
  {Nat.is_le(n, G.gen.left(first, B.cells(w, h))) == True{} : Bool}

def gen_inv(w, h, n, first, on, fits):
  match first:
    case T.Pos{fx, fy}:
      +p = {T.Pos{fx, fy} : T.Pos}
      +gl = G.gen.left(p, B.cells(w, h))
      +xw = P.and_true_l(Nat.is_lt(fx, w), Nat.is_lt(fy, h), on)
      +yh = P.and_true_r(Nat.is_lt(fx, w), Nat.is_lt(fy, h), on)
      +f1 = Equal.trans(Nat, firsts(p, B.cells(w, h)), cnt(fy, List.range(h)), 1n,
        firsts_rows(fx, fy, w, List.range(h), one_when(fx, w, xw)), one_when(fy, h, yh))
      +len = Equal.trans(Nat, List.length(&2, T.Pos, B.cells(w, h)),
        Nat.mul(List.length(&2, Nat, List.range(h)), w), Nat.mul(w, h),
        cells_go_len(w, List.range(h)),
        %Equal.sym(Nat, List.length(&2, Nat, List.range(h)), h, P.range_length(h)) :
          {Nat.mul(_, w) == Nat.mul(w, h) : Nat};
          P.mul_comm(h, w))
      +e1 = {%f1 : {Nat.add(gl, _) == List.length(&2, T.Pos, B.cells(w, h)) : Nat};
        gen_left_firsts(p, B.cells(w, h)) : {Nat.add(gl, 1n) == List.length(&2, T.Pos, B.cells(w, h)) : Nat}}
      +e2 = Equal.trans(Nat, 1n+gl, Nat.add(gl, 1n), Nat.mul(w, h),
        Equal.sym(Nat, Nat.add(gl, 1n), 1n+gl, P.add_one(gl)),
        Equal.trans(Nat, Nat.add(gl, 1n), List.length(&2, T.Pos, B.cells(w, h)), Nat.mul(w, h), e1, len))
      P.lt_succ_le(n, gl,
        {%Equal.sym(Nat, 1n+gl, Nat.mul(w, h), e2) : {Nat.is_lt(n, _) == True{} : Bool};
          fits : {Nat.is_lt(n, 1n+gl) == True{} : Bool}})

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
  gen_rows_count(first, w, List.range(h),
    {G.GenState{n, G.gen.left(first, B.cells(w, h)), rs} : G.GenState},
    gen_inv(w, h, n, first, on, fits), {==})
