import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG
import ./proof_copy.bend as PC
import ./proof_lists.bend as PL
import ./proof_cells.bend as PS
import ./proof_walk.bend as PW

# Lemmas about the flood (G.flood), for a fixed board w, h, layout.

# Reading a revealed cell after setting a cell to True
# ===================================================

def at_true_self.col(+r: List<&2, Bool>, +x: Nat, +b: Bool,
  be: {Nat.is_lt(x, List.length(&2, Bool, r)) == b : Bool},
  e: {Maybe.default(&2, Bool, List.get(&2, Bool, r, x), False{}) == True{} : Bool}) ->
  {Maybe.default(&2, Bool, List.get(&2, Bool, List.set(&2, Bool, r, x, True{}), x), False{}) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Bool>, List.get(&2, Bool, List.set(&2, Bool, r, x, True{}), x), Some{True{}},
        PL.get_set_eq(Bool, r, x, True{}, be)) : {Maybe.default(&2, Bool, _, False{}) == True{} : Bool}
      {==}
    case False{}:
      Empty.absurd({Maybe.default(&2, Bool, List.get(&2, Bool, List.set(&2, Bool, r, x, True{}), x), False{}) == True{} : Bool},
        P.false_ne_true(%P.get_out(Bool, r, x, be) :
          {Maybe.default(&2, Bool, _, False{}) == True{} : Bool}; e))

def at_true_self.row(+g: T.Grid(Bool), +x: Nat, +y: Nat, +b: Bool,
  be: {Nat.is_lt(y, List.length(&2, List<&2, Bool>, g)) == b : Bool},
  e: {B.at(Bool, False{}, g, T.Pos{x, y}) == True{} : Bool}) ->
  {B.at(Bool, False{}, B.set_at(Bool, g, T.Pos{x, y}, True{}), T.Pos{x, y}) == True{} : Bool}:
  match b:
    case True{}:
      +r = PL.row_of(Bool, g, y)
      +r2 = List.set(&2, Bool, r, x, True{})
      %Equal.sym(Maybe<&2, List<&2, Bool>>, List.get(&2, List<&2, Bool>, List.set(&2, List<&2, Bool>, g, y, r2), y),
        Some{r2}, PL.get_set_eq(List<&2, Bool>, g, y, r2, be)) :
        {Maybe.default(&2, Bool, List.get(&2, Bool, Maybe.default(&2, List<&2, Bool>, _, Nil{}), x), False{})
          == True{} : Bool}
      at_true_self.col(r, x, Nat.is_lt(x, List.length(&2, Bool, r)), {==}, e)
    case False{}:
      Empty.absurd({B.at(Bool, False{}, B.set_at(Bool, g, T.Pos{x, y}, True{}), T.Pos{x, y}) == True{} : Bool},
        P.false_ne_true(%P.get_out(List<&2, Bool>, g, y, be) :
          {Maybe.default(&2, Bool, List.get(&2, Bool, Maybe.default(&2, List<&2, Bool>, _, Nil{}), x), False{})
            == True{} : Bool}; e))

law at_true_self:
  for +g: T.Grid(Bool)
  for +q: T.Pos
  for e: {B.at(Bool, False{}, g, q) == True{} : Bool}
  {B.at(Bool, False{}, B.set_at(Bool, g, q, True{}), q) == True{} : Bool}

def at_true_self(g, q, e):
  match q:
    case T.Pos{x, y}:
      at_true_self.row(g, x, y, Nat.is_lt(y, List.length(&2, List<&2, Bool>, g)), {==}, e)

def at_set_mono.go(+g: T.Grid(Bool), +p: T.Pos, +q: T.Pos, e: {B.at(Bool, False{}, g, q) == True{} : Bool},
  +b: Bool, be: {B.same(p, q) == b : Bool}) ->
  {B.at(Bool, False{}, B.set_at(Bool, g, p, True{}), q) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(T.Pos, p, q, PG.same_sound(p, q, be)) :
        {B.at(Bool, False{}, B.set_at(Bool, g, _, True{}), q) == True{} : Bool}
      at_true_self(g, q, e)
    case False{}:
      %Equal.sym(Bool, B.at(Bool, False{}, B.set_at(Bool, g, p, True{}), q), B.at(Bool, False{}, g, q),
        PL.at_set_ne(Bool, g, p, q, True{}, False{}, be)) : {_ == True{} : Bool}
      e

# Revealing a cell keeps every revealed cell revealed.
law at_set_mono:
  for +g: T.Grid(Bool)
  for +p: T.Pos
  for +q: T.Pos
  for e: {B.at(Bool, False{}, g, q) == True{} : Bool}
  {B.at(Bool, False{}, B.set_at(Bool, g, p, True{}), q) == True{} : Bool}

def at_set_mono(g, p, q, e):
  at_set_mono.go(g, p, q, e, B.same(p, q), {==})

# Shape and monotonicity of the flood
# ===================================

law flood_shaped:
  for +n: Nat
  for +work: List<&2, G.Work>
  for +hd: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  {B.shaped(Bool, w, h, G.flood(n, work, hd, w, h, layout, shown)) == True{} : Bool}

def flood_shaped(n, work, hd, w, h, layout, shown, sh):
  match n:
    case 0n:
      sh
    case 1n+m:
      match work:
        case Nil{}:
          sh
        case G.Work{c, back} <> rest:
          match hd:
            case False{}:
              flood_shaped(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown, sh)
            case True{}:
              +s2 = B.set_at(Bool, shown, c, True{})
              +wk = G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest)
              flood_shaped(m, wk, G.head_hidden(w, h, s2, wk), w, h, layout, s2,
                PL.shaped_set(Bool, w, h, shown, c, True{}, sh))

law flood_mono:
  for +n: Nat
  for +work: List<&2, G.Work>
  for +hd: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +q: T.Pos
  for +s: {B.at(Bool, False{}, shown, q) == True{} : Bool}
  {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q) == True{} : Bool}

def flood_mono(n, work, hd, w, h, layout, shown, q, s):
  match n:
    case 0n:
      s
    case 1n+m:
      match work:
        case Nil{}:
          s
        case G.Work{c, back} <> rest:
          match hd:
            case False{}:
              flood_mono(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown, q, s)
            case True{}:
              +s2 = B.set_at(Bool, shown, c, True{})
              +wk = G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest)
              flood_mono(m, wk, G.head_hidden(w, h, s2, wk), w, h, layout, s2, q,
                at_set_mono(shown, c, q, s))

# The work list
# =============

# Some queued cell is q.
def wcontains(ws: List<&2, G.Work>, +q: T.Pos) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case G.Work{c, back} <> t:
      B.same(c, q) || wcontains(t, q)

def wcontains_append_r.go(+c: T.Pos, +xs: List<&2, G.Work>, +ys: List<&2, G.Work>, +q: T.Pos,
  ih: {wcontains(List.append(&2, G.Work, xs, ys), q) == True{} : Bool}) ->
  {Bool.or(B.same(c, q), wcontains(List.append(&2, G.Work, xs, ys), q)) == True{} : Bool}:
  %Equal.sym(Bool, wcontains(List.append(&2, G.Work, xs, ys), q), True{}, ih) :
    {Bool.or(B.same(c, q), _) == True{} : Bool}
  PS.or_true_r(B.same(c, q))

law wcontains_append_r:
  for +xs: List<&2, G.Work>
  for +ys: List<&2, G.Work>
  for +q: T.Pos
  for e: {wcontains(ys, q) == True{} : Bool}
  {wcontains(List.append(&2, G.Work, xs, ys), q) == True{} : Bool}

def wcontains_append_r(xs, ys, q, e):
  match xs:
    case Nil{}:
      e
    case G.Work{c, back} <> t:
      wcontains_append_r.go(c, t, ys, q, wcontains_append_r(t, ys, q, e))

def wcontains_append_l.go(+c: T.Pos, +t: List<&2, G.Work>, +ys: List<&2, G.Work>, +q: T.Pos, +b: Bool,
  e: {Bool.or(b, wcontains(t, q)) == True{} : Bool},
  ih: {wcontains(t, q) == True{} : Bool} -> {wcontains(List.append(&2, G.Work, t, ys), q) == True{} : Bool}) ->
  {Bool.or(b, wcontains(List.append(&2, G.Work, t, ys), q)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(e)

law wcontains_append_l:
  for +xs: List<&2, G.Work>
  for +ys: List<&2, G.Work>
  for +q: T.Pos
  for e: {wcontains(xs, q) == True{} : Bool}
  {wcontains(List.append(&2, G.Work, xs, ys), q) == True{} : Bool}

def wcontains_append_l(xs, ys, q, e):
  match xs:
    case Nil{}:
      Empty.absurd({wcontains(ys, q) == True{} : Bool}, P.false_ne_true(e))
    case G.Work{c, back} <> t:
      wcontains_append_l.go(c, t, ys, q, B.same(c, q), e, et => wcontains_append_l(t, ys, q, et))

def wcontains_works.go(+r0: T.Pos, +t: List<&2, T.Pos>, +back: List<&2, T.Pos>, +q: T.Pos, +b: Bool,
  e: {Bool.or(b, B.contains(t, q)) == True{} : Bool},
  ih: {B.contains(t, q) == True{} : Bool} -> {wcontains(G.works(t, back), q) == True{} : Bool}) ->
  {Bool.or(b, wcontains(G.works(t, back), q)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(e)

law wcontains_works:
  for +ns: List<&2, T.Pos>
  for +back: List<&2, T.Pos>
  for +q: T.Pos
  for e: {B.contains(ns, q) == True{} : Bool}
  {wcontains(G.works(ns, back), q) == True{} : Bool}

def wcontains_works(ns, back, q, e):
  match ns:
    case Nil{}:
      Empty.absurd({wcontains(Nil{}, q) == True{} : Bool}, P.false_ne_true(e))
    case r <> t:
      wcontains_works.go(r, t, back, q, B.same(r, q), e, et => wcontains_works(t, back, q, et))

law push_keeps:
  for +z: Bool
  for +ns: List<&2, T.Pos>
  for +back: List<&2, T.Pos>
  for +rest: List<&2, G.Work>
  for +q: T.Pos
  for e: {wcontains(rest, q) == True{} : Bool}
  {wcontains(G.push(z, ns, back, rest), q) == True{} : Bool}

def push_keeps(z, ns, back, rest, q, e):
  match z:
    case True{}:
      wcontains_append_r(G.works(ns, back), rest, q, e)
    case False{}:
      e

# Unrevealed cells
# ================

law unrev_on:
  for +w: Nat
  for +h: Nat
  for +shown: T.Grid(Bool)
  for +c: T.Pos
  for e: {G.unrevealed(w, h, shown, c) == True{} : Bool}
  {B.on_board(w, h, c) == True{} : Bool}

def unrev_on(w, h, shown, c, e):
  P.and_true_l(B.on_board(w, h, c), Bool.not(B.at(Bool, False{}, shown, c)), e)

law unrev_hidden:
  for +w: Nat
  for +h: Nat
  for +shown: T.Grid(Bool)
  for +c: T.Pos
  for e: {G.unrevealed(w, h, shown, c) == True{} : Bool}
  {B.at(Bool, False{}, shown, c) == False{} : Bool}

def unrev_hidden(w, h, shown, c, e):
  P.not_true(B.at(Bool, False{}, shown, c),
    P.and_true_r(B.on_board(w, h, c), Bool.not(B.at(Bool, False{}, shown, c)), e))

law unrev_shown:
  for +w: Nat
  for +h: Nat
  for +shown: T.Grid(Bool)
  for +c: T.Pos
  for e: {G.unrevealed(w, h, shown, c) == False{} : Bool}
  for on: {B.on_board(w, h, c) == True{} : Bool}
  {B.at(Bool, False{}, shown, c) == True{} : Bool}

def unrev_shown(w, h, shown, c, e, on):
  P.not_false(B.at(Bool, False{}, shown, c),
    %on : {Bool.and(_, Bool.not(B.at(Bool, False{}, shown, c))) == False{} : Bool}; e)

law count_after:
  for +w: Nat
  for +h: Nat
  for +shown: T.Grid(Bool)
  for +c: T.Pos
  for +m: Nat
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  for +u: {G.unrevealed(w, h, shown, c) == True{} : Bool}
  for cnt: {1n+m == B.count_false(shown) : Nat}
  {m == B.count_false(B.set_at(Bool, shown, c, True{})) : Nat}

def count_after(w, h, shown, c, m, sh, u, cnt):
  match c:
    case T.Pos{x, y}:
      P.succ_inj(m, B.count_false(B.set_at(Bool, shown, T.Pos{x, y}, True{})),
        Equal.trans(Nat, 1n+m, B.count_false(shown), 1n+B.count_false(B.set_at(Bool, shown, T.Pos{x, y}, True{})),
          cnt, PL.count_false_set(w, h, shown, x, y, sh, unrev_on(w, h, shown, T.Pos{x, y}, u),
            unrev_hidden(w, h, shown, T.Pos{x, y}, u))))

law at_set_on:
  for +w: Nat
  for +h: Nat
  for +shown: T.Grid(Bool)
  for +c: T.Pos
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  for on: {B.on_board(w, h, c) == True{} : Bool}
  {B.at(Bool, False{}, B.set_at(Bool, shown, c, True{}), c) == True{} : Bool}

def at_set_on(w, h, shown, c, sh, on):
  match c:
    case T.Pos{x, y}:
      PL.at_set_eq(Bool, w, h, shown, x, y, True{}, False{}, sh, on)

law cf_zero:
  for +w: Nat
  for +h: Nat
  for +shown: T.Grid(Bool)
  for +q: T.Pos
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  for on: {B.on_board(w, h, q) == True{} : Bool}
  for z: {0n == B.count_false(shown) : Nat}
  {B.at(Bool, False{}, shown, q) == True{} : Bool}

def cf_zero(w, h, shown, q, sh, on, z):
  match q:
    case T.Pos{x, y}:
      PL.count_false_zero(w, h, shown, x, y, sh, on, Equal.sym(Nat, 0n, B.count_false(shown), z))

# Every queued cell of the board
# ==============================

def flood_work.skip(+n: Nat, +c: T.Pos, +rest: List<&2, G.Work>, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +q: T.Pos, on: {B.on_board(w, h, q) == True{} : Bool},
  he: {G.unrevealed(w, h, shown, c) == False{} : Bool}, +b: Bool, be: {B.same(c, q) == b : Bool},
  m: {Bool.or(b, wcontains(rest, q)) == True{} : Bool},
  ih: {wcontains(rest, q) == True{} : Bool} ->
    {B.at(Bool, False{}, G.flood(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown), q) == True{} : Bool}) ->
  {B.at(Bool, False{}, G.flood(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown), q) == True{} : Bool}:
  match b:
    case True{}:
      +cq = PG.same_sound(c, q, be)
      flood_mono(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown, q,
        unrev_shown(w, h, shown, q, %cq : {G.unrevealed(w, h, shown, _) == False{} : Bool}; he, on))
    case False{}:
      ih(m)

def flood_work.take(+m: Nat, +c: T.Pos, +wk: List<&2, G.Work>, +rest: List<&2, G.Work>, +w: Nat, +h: Nat,
  +layout: T.Grid(Bool), +shown: T.Grid(Bool), +q: T.Pos,
  +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  he: {G.unrevealed(w, h, shown, c) == True{} : Bool},
  keep: {wcontains(rest, q) == True{} : Bool} -> {wcontains(wk, q) == True{} : Bool},
  +b: Bool, be: {B.same(c, q) == b : Bool}, m2: {Bool.or(b, wcontains(rest, q)) == True{} : Bool},
  ih: {wcontains(wk, q) == True{} : Bool} ->
    {B.at(Bool, False{}, G.flood(m, wk, G.head_hidden(w, h, B.set_at(Bool, shown, c, True{}), wk), w, h, layout,
      B.set_at(Bool, shown, c, True{})), q) == True{} : Bool}) ->
  {B.at(Bool, False{}, G.flood(m, wk, G.head_hidden(w, h, B.set_at(Bool, shown, c, True{}), wk), w, h, layout,
    B.set_at(Bool, shown, c, True{})), q) == True{} : Bool}:
  match b:
    case True{}:
      +cq = PG.same_sound(c, q, be)
      +s2 = B.set_at(Bool, shown, c, True{})
      flood_mono(m, wk, G.head_hidden(w, h, s2, wk), w, h, layout, s2, q,
        %cq : {B.at(Bool, False{}, s2, _) == True{} : Bool};
        at_set_on(w, h, shown, c, sh, unrev_on(w, h, shown, c, he)))
    case False{}:
      ih(keep(m2))

# A queued cell of the board ends up revealed (given n counts the
# unrevealed cells).
law flood_work:
  for +n: Nat
  for +work: List<&2, G.Work>
  for +hd: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  for +cnt: {n == B.count_false(shown) : Nat}
  for +he: {G.head_hidden(w, h, shown, work) == hd : Bool}
  for +q: T.Pos
  for +on: {B.on_board(w, h, q) == True{} : Bool}
  for m: {wcontains(work, q) == True{} : Bool}
  {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q) == True{} : Bool}

def flood_work(n, work, hd, w, h, layout, shown, sh, cnt, he, q, on, m):
  match n:
    case 0n:
      cf_zero(w, h, shown, q, sh, on, cnt)
    case 1n+k:
      match work:
        case Nil{}:
          Empty.absurd({B.at(Bool, False{}, shown, q) == True{} : Bool}, P.false_ne_true(m))
        case G.Work{c, back} <> rest:
          match hd:
            case False{}:
              flood_work.skip(n, c, rest, w, h, layout, shown, q, on, he, B.same(c, q), {==}, m,
                mr => flood_work(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown, sh, cnt, {==},
                  q, on, mr))
            case True{}:
              +s2 = B.set_at(Bool, shown, c, True{})
              +z = B.zero(w, h, layout, c)
              +ns = B.neighbours(w, h, c)
              +wk = G.push(z, ns, back, rest)
              flood_work.take(k, c, wk, rest, w, h, layout, shown, q, sh, he,
                mr => push_keeps(z, ns, back, rest, q, mr), B.same(c, q), {==}, m,
                mw => flood_work(k, wk, G.head_hidden(w, h, s2, wk), w, h, layout, s2,
                  PL.shaped_set(Bool, w, h, shown, c, True{}, sh), count_after(w, h, shown, c, k, sh, he, cnt),
                  {==}, q, on, mw))

# A newly revealed zero has its neighbours revealed
# =================================================

def both_absurd(-A: Type, +a: Bool, e1: {a == False{} : Bool}, e2: {a == True{} : Bool}) -> A:
  Empty.absurd(A, P.false_ne_true(Equal.trans(Bool, False{}, a, True{}, Equal.sym(Bool, a, False{}, e1), e2)))

def flood_zero.take(+k: Nat, +c: T.Pos, +back: List<&2, T.Pos>, +rest: List<&2, G.Work>, +w: Nat, +h: Nat,
  +layout: T.Grid(Bool), +shown: T.Grid(Bool), +q: T.Pos, +r: T.Pos,
  +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +cnt: {1n+k == B.count_false(shown) : Nat},
  +he: {G.unrevealed(w, h, shown, c) == True{} : Bool},
  before: {B.at(Bool, False{}, shown, q) == False{} : Bool},
  z: {B.zero(w, h, layout, q) == True{} : Bool},
  +rm: {B.contains(B.neighbours(w, h, q), r) == True{} : Bool},
  +b: Bool, +be: {B.same(c, q) == b : Bool},
  ih: {B.at(Bool, False{}, B.set_at(Bool, shown, c, True{}), q) == False{} : Bool} ->
    {B.at(Bool, False{}, G.flood(k, G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest),
      G.head_hidden(w, h, B.set_at(Bool, shown, c, True{}), G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest)),
      w, h, layout, B.set_at(Bool, shown, c, True{})), r) == True{} : Bool}) ->
  {B.at(Bool, False{}, G.flood(k, G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest),
    G.head_hidden(w, h, B.set_at(Bool, shown, c, True{}), G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest)),
    w, h, layout, B.set_at(Bool, shown, c, True{})), r) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(T.Pos, c, q, PG.same_sound(c, q, be)) :
        {B.at(Bool, False{}, G.flood(k, G.push(B.zero(w, h, layout, _), B.neighbours(w, h, _), back, rest),
          G.head_hidden(w, h, B.set_at(Bool, shown, _, True{}), G.push(B.zero(w, h, layout, _), B.neighbours(w, h, _), back, rest)),
          w, h, layout, B.set_at(Bool, shown, _, True{})), r) == True{} : Bool}
      %Equal.sym(Bool, B.zero(w, h, layout, q), True{}, z) :
        {B.at(Bool, False{}, G.flood(k, G.push(_, B.neighbours(w, h, q), back, rest),
          G.head_hidden(w, h, B.set_at(Bool, shown, q, True{}), G.push(_, B.neighbours(w, h, q), back, rest)),
          w, h, layout, B.set_at(Bool, shown, q, True{})), r) == True{} : Bool}
      +s2 = B.set_at(Bool, shown, q, True{})
      +wk = List.append(&2, G.Work, G.works(B.neighbours(w, h, q), back), rest)
      +hq = {%PG.same_sound(c, q, be) : {G.unrevealed(w, h, shown, _) == True{} : Bool};
        he : {G.unrevealed(w, h, shown, q) == True{} : Bool}}
      +ron = P.and_true_r(B.adjacent(q, r), B.on_board(w, h, r),
        PS.allp_member(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, q}, B.neighbours(w, h, q), r,
          PS.neighbours_all(w, h, q), rm))
      flood_work(k, wk, G.head_hidden(w, h, s2, wk), w, h, layout, s2,
        PL.shaped_set(Bool, w, h, shown, q, True{}, sh), count_after(w, h, shown, q, k, sh, hq, cnt), {==}, r, ron,
        wcontains_append_l(G.works(B.neighbours(w, h, q), back), rest, r,
          wcontains_works(B.neighbours(w, h, q), back, r, rm)))
    case False{}:
      ih(%Equal.sym(Bool, B.at(Bool, False{}, B.set_at(Bool, shown, c, True{}), q), B.at(Bool, False{}, shown, q),
        PL.at_set_ne(Bool, shown, c, q, True{}, False{}, be)) : {_ == False{} : Bool}; before)

law flood_zero:
  for +n: Nat
  for +work: List<&2, G.Work>
  for +hd: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  for +cnt: {n == B.count_false(shown) : Nat}
  for +he: {G.head_hidden(w, h, shown, work) == hd : Bool}
  for +q: T.Pos
  for +before: {B.at(Bool, False{}, shown, q) == False{} : Bool}
  for +after: {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q) == True{} : Bool}
  for +z: {B.zero(w, h, layout, q) == True{} : Bool}
  for +r: T.Pos
  for +rm: {B.contains(B.neighbours(w, h, q), r) == True{} : Bool}
  {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), r) == True{} : Bool}

def flood_zero(n, work, hd, w, h, layout, shown, sh, cnt, he, q, before, after, z, r, rm):
  match n:
    case 0n:
      both_absurd({B.at(Bool, False{}, shown, r) == True{} : Bool}, B.at(Bool, False{}, shown, q), before, after)
    case 1n+k:
      match work:
        case Nil{}:
          both_absurd({B.at(Bool, False{}, shown, r) == True{} : Bool}, B.at(Bool, False{}, shown, q), before, after)
        case G.Work{c, back} <> rest:
          match hd:
            case False{}:
              flood_zero(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown, sh, cnt, {==}, q,
                before, after, z, r, rm)
            case True{}:
              +s2 = B.set_at(Bool, shown, c, True{})
              +wk = G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest)
              flood_zero.take(k, c, back, rest, w, h, layout, shown, q, r, sh, cnt, he, before, z, rm,
                B.same(c, q), {==},
                b2 => flood_zero(k, wk, G.head_hidden(w, h, s2, wk), w, h, layout, s2,
                  PL.shaped_set(Bool, w, h, shown, c, True{}, sh), count_after(w, h, shown, c, k, sh, he, cnt),
                  {==}, q, b2, after, z, r, rm))

# Every newly revealed cell has a zero walk from the first cell
# =============================================================

# Each queued cell's ghost path is a zero walk from p0 to it.
def works_ok(ws: List<&2, G.Work>, +w: Nat, +h: Nat, +layout: T.Grid(Bool), +p0: T.Pos) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case G.Work{c, back} <> t:
      L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c) && works_ok(t, w, h, layout, p0)

law works_ok_append:
  for +xs: List<&2, G.Work>
  for +ys: List<&2, G.Work>
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p0: T.Pos
  for +a: {works_ok(xs, w, h, layout, p0) == True{} : Bool}
  for b: {works_ok(ys, w, h, layout, p0) == True{} : Bool}
  {works_ok(List.append(&2, G.Work, xs, ys), w, h, layout, p0) == True{} : Bool}

def works_ok_append(xs, ys, w, h, layout, p0, a, b):
  match xs:
    case Nil{}:
      b
    case G.Work{c, back} <> t:
      +hd = L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c)
      %Equal.sym(Bool, hd, True{}, P.and_true_l(hd, works_ok(t, w, h, layout, p0), a)) :
        {Bool.and(_, works_ok(List.append(&2, G.Work, t, ys), w, h, layout, p0)) == True{} : Bool}
      works_ok_append(t, ys, w, h, layout, p0, P.and_true_r(hd, works_ok(t, w, h, layout, p0), a), b)

law works_ok_works:
  for +ns: List<&2, T.Pos>
  for +back: List<&2, T.Pos>
  for +c: T.Pos
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p0: T.Pos
  for +okc: {L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c) == True{} : Bool}
  for +zc: {L.zero(w, h, layout, c) == True{} : Bool}
  for +adj: {PS.allp(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, c}, ns) == True{} : Bool}
  {works_ok(G.works(ns, back), w, h, layout, p0) == True{} : Bool}

def works_ok_works(ns, back, c, w, h, layout, p0, okc, zc, adj):
  match ns:
    case Nil{}:
      {==}
    case r <> t:
      +ar = PS.allp_head(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, c}, r, t, adj)
      +a1 = P.and_true_l(B.adjacent(c, r), B.on_board(w, h, r), ar)
      +a2 = P.and_true_r(B.adjacent(c, r), B.on_board(w, h, r), ar)
      +wr = PW.walk_snoc(List.reverse(&2, T.Pos, back), w, h, layout, p0, c, r, okc, zc,
        %PC.adjacent_eq(c, r) : {_ == True{} : Bool}; a1,
        %PC.on_board_eq(w, h, r) : {_ == True{} : Bool}; a2)
      %Equal.sym(Bool, L.zero_walk(List.reverse(&2, T.Pos, r <> back), w, h, layout, p0, r), True{},
        %Equal.sym(List<&2, T.Pos>, List.reverse(&2, T.Pos, r <> back),
          List.append(&2, T.Pos, List.reverse(&2, T.Pos, back), [r]), PW.rev_cons(T.Pos, r, back)) :
          {L.zero_walk(_, w, h, layout, p0, r) == True{} : Bool}; wr) :
        {Bool.and(_, works_ok(G.works(t, back), w, h, layout, p0)) == True{} : Bool}
      works_ok_works(t, back, c, w, h, layout, p0, okc, zc,
        PS.allp_tail(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, c}, r, t, adj))

def works_ok_push(+z: Bool, +c: T.Pos, +back: List<&2, T.Pos>, +rest: List<&2, G.Work>, +w: Nat, +h: Nat,
  +layout: T.Grid(Bool), +p0: T.Pos, ze: {B.zero(w, h, layout, c) == z : Bool},
  okc: {L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c) == True{} : Bool},
  okr: {works_ok(rest, w, h, layout, p0) == True{} : Bool}) ->
  {works_ok(G.push(z, B.neighbours(w, h, c), back, rest), w, h, layout, p0) == True{} : Bool}:
  match z:
    case True{}:
      works_ok_append(G.works(B.neighbours(w, h, c), back), rest, w, h, layout, p0,
        works_ok_works(B.neighbours(w, h, c), back, c, w, h, layout, p0, okc,
          %PC.zero_eq(w, h, layout, c) : {_ == True{} : Bool}; ze,
          PS.neighbours_all(w, h, c)), okr)
    case False{}:
      okr

def Walk(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +p0: T.Pos, +q: T.Pos) -> Type:
  Exists(List<&2, T.Pos>, path => {L.zero_walk(path, w, h, layout, p0, q) == True{} : Bool})

def flood_path.take(+c: T.Pos, +back: List<&2, T.Pos>, +rest: List<&2, G.Work>, +w: Nat, +h: Nat,
  +layout: T.Grid(Bool), +shown: T.Grid(Bool), +p0: T.Pos, +q: T.Pos,
  +ok: {Bool.and(L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c), works_ok(rest, w, h, layout, p0)) == True{} : Bool},
  before: {B.at(Bool, False{}, shown, q) == False{} : Bool}, +b: Bool, be: {B.same(c, q) == b : Bool},
  ih: {works_ok(G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest), w, h, layout, p0) == True{} : Bool} ->
    {B.at(Bool, False{}, B.set_at(Bool, shown, c, True{}), q) == False{} : Bool} -> Walk(w, h, layout, p0, q)) ->
  Walk(w, h, layout, p0, q):
  match b:
    case True{}:
      +hd = L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c)
      +okc = P.and_true_l(hd, works_ok(rest, w, h, layout, p0), ok)
      (List.reverse(&2, T.Pos, back),
        %PG.same_sound(c, q, be) : {L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, _) == True{} : Bool};
        okc)
    case False{}:
      +hd = L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c)
      +okc = P.and_true_l(hd, works_ok(rest, w, h, layout, p0), ok)
      ih(works_ok_push(B.zero(w, h, layout, c), c, back, rest, w, h, layout, p0, {==}, okc,
          P.and_true_r(hd, works_ok(rest, w, h, layout, p0), ok)),
        %Equal.sym(Bool, B.at(Bool, False{}, B.set_at(Bool, shown, c, True{}), q), B.at(Bool, False{}, shown, q),
          PL.at_set_ne(Bool, shown, c, q, True{}, False{}, be)) : {_ == False{} : Bool}; before)

law flood_path:
  for +n: Nat
  for +work: List<&2, G.Work>
  for +hd: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +p0: T.Pos
  for +ok: {works_ok(work, w, h, layout, p0) == True{} : Bool}
  for +q: T.Pos
  for +before: {B.at(Bool, False{}, shown, q) == False{} : Bool}
  for +after: {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q) == True{} : Bool}
  Walk(w, h, layout, p0, q)

def flood_path(n, work, hd, w, h, layout, shown, p0, ok, q, before, after):
  match n:
    case 0n:
      both_absurd(Walk(w, h, layout, p0, q), B.at(Bool, False{}, shown, q), before, after)
    case 1n+k:
      match work:
        case Nil{}:
          both_absurd(Walk(w, h, layout, p0, q), B.at(Bool, False{}, shown, q), before, after)
        case G.Work{c, back} <> rest:
          match hd:
            case False{}:
              flood_path(n, rest, G.head_hidden(w, h, shown, rest), w, h, layout, shown, p0,
                P.and_true_r(L.zero_walk(List.reverse(&2, T.Pos, back), w, h, layout, p0, c),
                  works_ok(rest, w, h, layout, p0), ok), q, before, after)
            case True{}:
              +s2 = B.set_at(Bool, shown, c, True{})
              +wk = G.push(B.zero(w, h, layout, c), B.neighbours(w, h, c), back, rest)
              flood_path.take(c, back, rest, w, h, layout, shown, p0, q, ok, before, B.same(c, q), {==},
                okw => b2 => flood_path(k, wk, G.head_hidden(w, h, s2, wk), w, h, layout, s2, p0, okw, q, b2, after))
