import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G
import ./LAWS.bend as L
import ./proof_base.bend as P

# Lemmas about the knowledge the game builds.

def Maybe.disc_none(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def know_row_get.none(-A: Data, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %e : Maybe.disc_none(A, _)
  Unit{}

def Maybe.value(-A: Data, +d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def know_row_get.some(-A: Data, +a: A, +x: A, e: {Some{a} == Some{x} : Maybe<&2, A>}) ->
  {a == x : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.value(A, a, m), Some{a}, Some{x}, e)

law know_row_get:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +y: Nat
  for +xs: List<&2, Nat>
  for +j: Nat
  for +x: Nat
  for e: {List.get(&2, Nat, xs, j) == Some{x} : Maybe<&2, Nat>}
  {List.get(&2, T.Seen, G.know_row(w, h, layout, shown, y, xs), j)
    == Some{G.seen_at(w, h, layout, shown, T.Pos{x, y})} : Maybe<&2, T.Seen>}

def know_row_get(w, h, layout, shown, y, xs, j, x, e):
  match xs j:
    case Nil{} _:
      Empty.absurd({List.get(&2, T.Seen, G.know_row(w, h, layout, shown, y, Nil{}), j)
        == Some{G.seen_at(w, h, layout, shown, T.Pos{x, y})} : Maybe<&2, T.Seen>},
        know_row_get.none(Nat, x, e))
    case a <> t 0n:
      %know_row_get.some(Nat, a, x, e) :
        {Some{G.seen_at(w, h, layout, shown, T.Pos{a, y})}
          == Some{G.seen_at(w, h, layout, shown, T.Pos{_, y})} : Maybe<&2, T.Seen>}
      {==}
    case a <> t 1n+k:
      know_row_get(w, h, layout, shown, y, t, k, x, e)


law know_rows_get:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +ys: List<&2, Nat>
  for +i: Nat
  for +y: Nat
  for e: {List.get(&2, Nat, ys, i) == Some{y} : Maybe<&2, Nat>}
  {List.get(&2, List<&2, T.Seen>, G.know_rows(w, h, layout, shown, ys), i)
    == Some{G.know_row(w, h, layout, shown, y, List.range(w))} : Maybe<&2, List<&2, T.Seen>>}

def know_rows_get(w, h, layout, shown, ys, i, y, e):
  match ys i:
    case Nil{} _:
      Empty.absurd({List.get(&2, List<&2, T.Seen>, G.know_rows(w, h, layout, shown, Nil{}), i)
        == Some{G.know_row(w, h, layout, shown, y, List.range(w))} : Maybe<&2, List<&2, T.Seen>>},
        know_row_get.none(Nat, y, e))
    case a <> t 0n:
      %know_row_get.some(Nat, a, y, e) :
        {Some{G.know_row(w, h, layout, shown, a, List.range(w))}
          == Some{G.know_row(w, h, layout, shown, _, List.range(w))} : Maybe<&2, List<&2, T.Seen>>}
      {==}
    case a <> t 1n+k:
      know_rows_get(w, h, layout, shown, t, k, y, e)

# On the board, the knowledge shows what seen_at says.
law know_at:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +x: Nat
  for +y: Nat
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  {L.at(T.Seen, T.Hidden{}, G.know_rows(w, h, layout, shown, List.range(h)), T.Pos{x, y})
    == G.seen_at(w, h, layout, shown, T.Pos{x, y}) : T.Seen}

def know_at(w, h, layout, shown, x, y, on):
  +xw = P.and_true_l(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +yh = P.and_true_r(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +rows = G.know_rows(w, h, layout, shown, List.range(h))
  +row = G.know_row(w, h, layout, shown, y, List.range(w))
  %Equal.sym(Maybe<&2, List<&2, T.Seen>>, List.get(&2, List<&2, T.Seen>, rows, y), Some{row},
    know_rows_get(w, h, layout, shown, List.range(h), y, y, P.range_get(h, y, yh))) :
    {Maybe.default(&2, T.Seen, List.get(&2, T.Seen,
      Maybe.default(&2, List<&2, T.Seen>, _, Nil{}), x), T.Hidden{})
      == G.seen_at(w, h, layout, shown, T.Pos{x, y}) : T.Seen}
  %Equal.sym(Maybe<&2, T.Seen>, List.get(&2, T.Seen, row, x),
    Some{G.seen_at(w, h, layout, shown, T.Pos{x, y})},
    know_row_get(w, h, layout, shown, y, List.range(w), x, x, P.range_get(w, x, xw))) :
    {Maybe.default(&2, T.Seen, _, T.Hidden{})
      == G.seen_at(w, h, layout, shown, T.Pos{x, y}) : T.Seen}
  {==}

law hidden_pick:
  for +c: Bool
  for +m: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  {L.is_hidden(G.seen_pick(c, m, w, h, layout, p)) == Bool.not(c) : Bool}

def hidden_pick(c, m, w, h, layout, p):
  match c m:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}

def know_hidden.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool),
  +x: Nat, +y: Nat, +b: Bool, +e: {B.on_board(w, h, T.Pos{x, y}) == b : Bool}) ->
  {Bool.and(B.on_board(w, h, T.Pos{x, y}),
     L.is_hidden(L.at(T.Seen, T.Hidden{}, G.know_rows(w, h, layout, shown, List.range(h)), T.Pos{x, y})))
   == Bool.and(B.on_board(w, h, T.Pos{x, y}), Bool.not(B.at(Bool, False{}, shown, T.Pos{x, y})))
   : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, B.on_board(w, h, T.Pos{x, y}), False{}, e) :
        {Bool.and(_, L.is_hidden(L.at(T.Seen, T.Hidden{}, G.know_rows(w, h, layout, shown, List.range(h)), T.Pos{x, y})))
          == Bool.and(_, Bool.not(B.at(Bool, False{}, shown, T.Pos{x, y}))) : Bool}
      {==}
    case True{}:
      +rows = G.know_rows(w, h, layout, shown, List.range(h))
      +p = {T.Pos{x, y} : T.Pos}
      %Equal.sym(Bool, B.on_board(w, h, p), True{}, e) :
        {Bool.and(_, L.is_hidden(L.at(T.Seen, T.Hidden{}, rows, p)))
          == Bool.and(_, Bool.not(B.at(Bool, False{}, shown, p))) : Bool}
      %Equal.sym(T.Seen, L.at(T.Seen, T.Hidden{}, rows, p), G.seen_at(w, h, layout, shown, p),
        know_at(w, h, layout, shown, x, y, e)) :
        {L.is_hidden(_) == Bool.not(B.at(Bool, False{}, shown, p)) : Bool}
      hidden_pick(B.at(Bool, False{}, shown, p), B.mine(layout, p), w, h, layout, p)

# Hidden in the knowledge means on the board and not revealed in the game.
law know_hidden:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +status: T.Status
  for +p: T.Pos
  {L.hidden(G.knowledge(G.Game{w, h, layout, shown, flags, status}), p)
    == G.unrevealed(w, h, shown, p) : Bool}

def know_hidden(w, h, layout, shown, flags, status, p):
  match p:
    case T.Pos{x, y}:
      know_hidden.go(w, h, layout, shown, x, y, B.on_board(w, h, T.Pos{x, y}), {==})

# Cells and the flag list
# =======================

law same_refl:
  for +p: T.Pos
  {B.same(p, p) == True{} : Bool}

def same_refl(p):
  match p:
    case T.Pos{x, y}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, P.eq_refl(x)) :
        {Bool.and(_, Nat.is_eq(y, y)) == True{} : Bool}
      P.eq_refl(y)

law same_sound:
  for +p: T.Pos
  for +q: T.Pos
  for +e: {B.same(p, q) == True{} : Bool}
  {p == q : T.Pos}

def same_sound(p, q, e):
  match p q:
    case T.Pos{px, py} T.Pos{qx, qy}:
      +ex = P.eq_sound(px, qx, P.and_true_l(Nat.is_eq(px, qx), Nat.is_eq(py, qy), e))
      +ey = P.eq_sound(py, qy, P.and_true_r(Nat.is_eq(px, qx), Nat.is_eq(py, qy), e))
      %ex : {T.Pos{px, py} == T.Pos{_, qy} : T.Pos}
      %ey : {T.Pos{px, py} == T.Pos{px, _} : T.Pos}
      {==}

def same_ne.go(+p: T.Pos, +q: T.Pos, ne: {p != q : T.Pos}, b: Bool,
  e: {B.same(p, q) == b : Bool}) -> {B.same(p, q) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      Empty.absurd({B.same(p, q) == False{} : Bool}, ne(same_sound(p, q, e)))

law same_ne:
  for +p: T.Pos
  for +q: T.Pos
  for ne: {p != q : T.Pos}
  {B.same(p, q) == False{} : Bool}

def same_ne(p, q, ne):
  same_ne.go(p, q, ne, B.same(p, q), {==})

law contains_cons_self:
  for +p: T.Pos
  for +xs: List<&2, T.Pos>
  {B.contains(p <> xs, p) == True{} : Bool}

def contains_cons_self(p, xs):
  %Equal.sym(Bool, B.same(p, p), True{}, same_refl(p)) :
    {Bool.or(_, B.contains(xs, p)) == True{} : Bool}
  {==}

def contains_remove_self.go(+q: T.Pos, +t: List<&2, T.Pos>, +p: T.Pos, +b: Bool,
  +e: {B.same(q, p) == b : Bool},
  ih: {B.contains(B.remove(t, p), p) == False{} : Bool}) ->
  {B.contains(List.filter.put(T.Pos, q, B.remove(t, p), Bool.not(B.same(q, p))), p)
    == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, B.same(q, p), True{}, e) :
        {B.contains(List.filter.put(T.Pos, q, B.remove(t, p), Bool.not(_)), p) == False{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, B.same(q, p), False{}, e) :
        {B.contains(List.filter.put(T.Pos, q, B.remove(t, p), Bool.not(_)), p) == False{} : Bool}
      %Equal.sym(Bool, B.same(q, p), False{}, e) :
        {Bool.or(_, B.contains(B.remove(t, p), p)) == False{} : Bool}
      ih

law contains_remove_self:
  for +xs: List<&2, T.Pos>
  for +p: T.Pos
  {B.contains(B.remove(xs, p), p) == False{} : Bool}

def contains_remove_self(xs, p):
  match xs:
    case Nil{}:
      {==}
    case q <> t:
      contains_remove_self.go(q, t, p, B.same(q, p), {==}, contains_remove_self(t, p))

def contains_remove_other.go(+e0: T.Pos, +t: List<&2, T.Pos>, +p: T.Pos, +q: T.Pos,
  d: {B.same(p, q) == False{} : Bool}, +b: Bool, +e: {B.same(e0, p) == b : Bool},
  ih: {B.contains(B.remove(t, p), q) == B.contains(t, q) : Bool}) ->
  {B.contains(List.filter.put(T.Pos, e0, B.remove(t, p), Bool.not(B.same(e0, p))), q)
    == Bool.or(B.same(e0, q), B.contains(t, q)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, B.same(e0, p), True{}, e) :
        {B.contains(List.filter.put(T.Pos, e0, B.remove(t, p), Bool.not(_)), q)
          == Bool.or(B.same(e0, q), B.contains(t, q)) : Bool}
      %Equal.sym(T.Pos, e0, p, same_sound(e0, p, e)) :
        {B.contains(B.remove(t, p), q) == Bool.or(B.same(_, q), B.contains(t, q)) : Bool}
      %Equal.sym(Bool, B.same(p, q), False{}, d) :
        {B.contains(B.remove(t, p), q) == Bool.or(_, B.contains(t, q)) : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, B.same(e0, p), False{}, e) :
        {B.contains(List.filter.put(T.Pos, e0, B.remove(t, p), Bool.not(_)), q)
          == Bool.or(B.same(e0, q), B.contains(t, q)) : Bool}
      %ih : {Bool.or(B.same(e0, q), B.contains(B.remove(t, p), q))
        == Bool.or(B.same(e0, q), _) : Bool}
      {==}

law contains_remove_other:
  for +xs: List<&2, T.Pos>
  for +p: T.Pos
  for +q: T.Pos
  for +d: {B.same(p, q) == False{} : Bool}
  {B.contains(B.remove(xs, p), q) == B.contains(xs, q) : Bool}

def contains_remove_other(xs, p, q, d):
  match xs:
    case Nil{}:
      {==}
    case e0 <> t:
      contains_remove_other.go(e0, t, p, q, d, B.same(e0, p), {==},
        contains_remove_other(t, p, q, d))

def toggle_self.go(+flags: List<&2, T.Pos>, +p: T.Pos, +c: Bool,
  e: {B.contains(flags, p) == c : Bool}) ->
  {B.contains(G.toggle.go(c, flags, p), p) == Bool.not(c) : Bool}:
  match c:
    case True{}:
      contains_remove_self(flags, p)
    case False{}:
      contains_cons_self(p, flags)

# Toggling p flips whether p is in the list.
law toggle_self:
  for +flags: List<&2, T.Pos>
  for +p: T.Pos
  {B.contains(G.toggle(flags, p), p) == Bool.not(B.contains(flags, p)) : Bool}

def toggle_self(flags, p):
  toggle_self.go(flags, p, B.contains(flags, p), {==})

def toggle_other.go(+flags: List<&2, T.Pos>, +p: T.Pos, +q: T.Pos,
  d: {B.same(p, q) == False{} : Bool}, +c: Bool) ->
  {B.contains(G.toggle.go(c, flags, p), q) == B.contains(flags, q) : Bool}:
  match c:
    case True{}:
      contains_remove_other(flags, p, q, d)
    case False{}:
      %Equal.sym(Bool, B.same(p, q), False{}, d) :
        {Bool.or(_, B.contains(flags, q)) == B.contains(flags, q) : Bool}
      {==}

# Toggling p leaves every other cell as it was.
law toggle_other:
  for +flags: List<&2, T.Pos>
  for +p: T.Pos
  for +q: T.Pos
  for +d: {B.same(p, q) == False{} : Bool}
  {B.contains(G.toggle(flags, p), q) == B.contains(flags, q) : Bool}

def toggle_other(flags, p, q, d):
  toggle_other.go(flags, p, q, d, B.contains(flags, p))
