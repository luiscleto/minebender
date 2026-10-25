import Base
import ./types.bend as T
import ./board.bend as B
import ./solver.bend as S
import ./proof_base.bend as P
import ./proof_lists.bend as PL
import ./proof_cells.bend as PS

# The counting search answers exactly as the plain one: dfs2, which carries
# the mines and unassigned cells of the partial layout, returns what dfs
# returns, as long as the counts start right and every cell it assigns is
# on the board.

# Counting after an assignment
# ============================

law row_none_set:
  for +r: List<&2, Maybe<&2, Bool>>
  for +x: Nat
  for +b: Bool
  for e: {List.get(&2, Maybe<&2, Bool>, r, x) == Some{None{}} : Maybe<&2, Maybe<&2, Bool>>}
  {S.row_none(r) == 1n+S.row_none(List.set(&2, Maybe<&2, Bool>, r, x, Some{b})) : Nat}

def row_none_set(r, x, b, e):
  match r x:
    case Nil{} _:
      Empty.absurd({0n == 1n+0n : Nat}, PL.none_ne_some(Maybe<&2, Bool>, None{}, e))
    case m <> t 0n:
      %Equal.sym(Maybe<&2, Bool>, m, None{}, PL.some_inj(Maybe<&2, Bool>, m, None{}, e)) :
        {Nat.add(S.one_if(S.is_none(_)), S.row_none(t)) == 1n+Nat.add(S.one_if(S.is_none(Some{b})), S.row_none(t)) : Nat}
      {==}
    case m <> t 1n+k:
      %Equal.sym(Nat, S.row_none(t), 1n+S.row_none(List.set(&2, Maybe<&2, Bool>, t, k, Some{b})), row_none_set(t, k, b, e)) :
        {Nat.add(S.one_if(S.is_none(m)), _)
          == 1n+Nat.add(S.one_if(S.is_none(m)), S.row_none(List.set(&2, Maybe<&2, Bool>, t, k, Some{b}))) : Nat}
      P.add_succ(S.one_if(S.is_none(m)), S.row_none(List.set(&2, Maybe<&2, Bool>, t, k, Some{b})))

law row_true_set_t:
  for +r: List<&2, Maybe<&2, Bool>>
  for +x: Nat
  for e: {List.get(&2, Maybe<&2, Bool>, r, x) == Some{None{}} : Maybe<&2, Maybe<&2, Bool>>}
  {S.row_true(List.set(&2, Maybe<&2, Bool>, r, x, Some{True{}})) == 1n+S.row_true(r) : Nat}

def row_true_set_t(r, x, e):
  match r x:
    case Nil{} _:
      Empty.absurd({0n == 1n+0n : Nat}, PL.none_ne_some(Maybe<&2, Bool>, None{}, e))
    case m <> t 0n:
      %Equal.sym(Maybe<&2, Bool>, m, None{}, PL.some_inj(Maybe<&2, Bool>, m, None{}, e)) :
        {Nat.add(S.one_if(S.is_true(Some{True{}})), S.row_true(t)) == 1n+Nat.add(S.one_if(S.is_true(_)), S.row_true(t)) : Nat}
      {==}
    case m <> t 1n+k:
      %Equal.sym(Nat, S.row_true(List.set(&2, Maybe<&2, Bool>, t, k, Some{True{}})), 1n+S.row_true(t), row_true_set_t(t, k, e)) :
        {Nat.add(S.one_if(S.is_true(m)), _) == 1n+Nat.add(S.one_if(S.is_true(m)), S.row_true(t)) : Nat}
      P.add_succ(S.one_if(S.is_true(m)), S.row_true(t))

law row_true_set_f:
  for +r: List<&2, Maybe<&2, Bool>>
  for +x: Nat
  for e: {List.get(&2, Maybe<&2, Bool>, r, x) == Some{None{}} : Maybe<&2, Maybe<&2, Bool>>}
  {S.row_true(List.set(&2, Maybe<&2, Bool>, r, x, Some{False{}})) == S.row_true(r) : Nat}

def row_true_set_f(r, x, e):
  match r x:
    case Nil{} _:
      Empty.absurd({0n == 0n : Nat}, PL.none_ne_some(Maybe<&2, Bool>, None{}, e))
    case m <> t 0n:
      %Equal.sym(Maybe<&2, Bool>, m, None{}, PL.some_inj(Maybe<&2, Bool>, m, None{}, e)) :
        {Nat.add(S.one_if(S.is_true(Some{False{}})), S.row_true(t)) == Nat.add(S.one_if(S.is_true(_)), S.row_true(t)) : Nat}
      {==}
    case m <> t 1n+k:
      %Equal.sym(Nat, S.row_true(List.set(&2, Maybe<&2, Bool>, t, k, Some{False{}})), S.row_true(t), row_true_set_f(t, k, e)) :
        {Nat.add(S.one_if(S.is_true(m)), _) == Nat.add(S.one_if(S.is_true(m)), S.row_true(t)) : Nat}
      {==}

law none_go:
  for +g: T.Grid(Maybe<&2, Bool>)
  for +y: Nat
  for +r: List<&2, Maybe<&2, Bool>>
  for +r2: List<&2, Maybe<&2, Bool>>
  for e: {List.get(&2, List<&2, Maybe<&2, Bool>>, g, y) == Some{r} : Maybe<&2, List<&2, Maybe<&2, Bool>>>}
  for rf: {S.row_none(r) == 1n+S.row_none(r2) : Nat}
  {S.part_none(g) == 1n+S.part_none(List.set(&2, List<&2, Maybe<&2, Bool>>, g, y, r2)) : Nat}

def none_go(g, y, r, r2, e, rf):
  match g y:
    case Nil{} _:
      Empty.absurd({0n == 1n+0n : Nat}, PL.none_ne_some(List<&2, Maybe<&2, Bool>>, r, e))
    case row <> t 0n:
      %Equal.sym(List<&2, Maybe<&2, Bool>>, row, r, PL.some_inj(List<&2, Maybe<&2, Bool>>, row, r, e)) :
        {Nat.add(S.row_none(_), S.part_none(t)) == 1n+Nat.add(S.row_none(r2), S.part_none(t)) : Nat}
      %Equal.sym(Nat, S.row_none(r), 1n+S.row_none(r2), rf) :
        {Nat.add(_, S.part_none(t)) == 1n+Nat.add(S.row_none(r2), S.part_none(t)) : Nat}
      {==}
    case row <> t 1n+k:
      %Equal.sym(Nat, S.part_none(t), 1n+S.part_none(List.set(&2, List<&2, Maybe<&2, Bool>>, t, k, r2)), none_go(t, k, r, r2, e, rf)) :
        {Nat.add(S.row_none(row), _)
          == 1n+Nat.add(S.row_none(row), S.part_none(List.set(&2, List<&2, Maybe<&2, Bool>>, t, k, r2))) : Nat}
      P.add_succ(S.row_none(row), S.part_none(List.set(&2, List<&2, Maybe<&2, Bool>>, t, k, r2)))

law true_go_t:
  for +g: T.Grid(Maybe<&2, Bool>)
  for +y: Nat
  for +r: List<&2, Maybe<&2, Bool>>
  for +r2: List<&2, Maybe<&2, Bool>>
  for e: {List.get(&2, List<&2, Maybe<&2, Bool>>, g, y) == Some{r} : Maybe<&2, List<&2, Maybe<&2, Bool>>>}
  for rf: {S.row_true(r2) == 1n+S.row_true(r) : Nat}
  {S.part_true(List.set(&2, List<&2, Maybe<&2, Bool>>, g, y, r2)) == 1n+S.part_true(g) : Nat}

def true_go_t(g, y, r, r2, e, rf):
  match g y:
    case Nil{} _:
      Empty.absurd({0n == 1n+0n : Nat}, PL.none_ne_some(List<&2, Maybe<&2, Bool>>, r, e))
    case row <> t 0n:
      %Equal.sym(List<&2, Maybe<&2, Bool>>, row, r, PL.some_inj(List<&2, Maybe<&2, Bool>>, row, r, e)) :
        {Nat.add(S.row_true(r2), S.part_true(t)) == 1n+Nat.add(S.row_true(_), S.part_true(t)) : Nat}
      %Equal.sym(Nat, S.row_true(r2), 1n+S.row_true(r), rf) :
        {Nat.add(_, S.part_true(t)) == 1n+Nat.add(S.row_true(r), S.part_true(t)) : Nat}
      {==}
    case row <> t 1n+k:
      %Equal.sym(Nat, S.part_true(List.set(&2, List<&2, Maybe<&2, Bool>>, t, k, r2)), 1n+S.part_true(t), true_go_t(t, k, r, r2, e, rf)) :
        {Nat.add(S.row_true(row), _) == 1n+Nat.add(S.row_true(row), S.part_true(t)) : Nat}
      P.add_succ(S.row_true(row), S.part_true(t))

law true_go_f:
  for +g: T.Grid(Maybe<&2, Bool>)
  for +y: Nat
  for +r: List<&2, Maybe<&2, Bool>>
  for +r2: List<&2, Maybe<&2, Bool>>
  for e: {List.get(&2, List<&2, Maybe<&2, Bool>>, g, y) == Some{r} : Maybe<&2, List<&2, Maybe<&2, Bool>>>}
  for rf: {S.row_true(r2) == S.row_true(r) : Nat}
  {S.part_true(List.set(&2, List<&2, Maybe<&2, Bool>>, g, y, r2)) == S.part_true(g) : Nat}

def true_go_f(g, y, r, r2, e, rf):
  match g y:
    case Nil{} _:
      Empty.absurd({0n == 0n : Nat}, PL.none_ne_some(List<&2, Maybe<&2, Bool>>, r, e))
    case row <> t 0n:
      %Equal.sym(List<&2, Maybe<&2, Bool>>, row, r, PL.some_inj(List<&2, Maybe<&2, Bool>>, row, r, e)) :
        {Nat.add(S.row_true(r2), S.part_true(t)) == Nat.add(S.row_true(_), S.part_true(t)) : Nat}
      %Equal.sym(Nat, S.row_true(r2), S.row_true(r), rf) :
        {Nat.add(_, S.part_true(t)) == Nat.add(S.row_true(r), S.part_true(t)) : Nat}
      {==}
    case row <> t 1n+k:
      %Equal.sym(Nat, S.part_true(List.set(&2, List<&2, Maybe<&2, Bool>>, t, k, r2)), S.part_true(t), true_go_f(t, k, r, r2, e, rf)) :
        {Nat.add(S.row_true(row), _) == Nat.add(S.row_true(row), S.part_true(t)) : Nat}
      {==}

# The row of an unassigned cell, and the cell in it.
def cell_none(+w: Nat, +h: Nat, +part: T.Grid(Maybe<&2, Bool>), +x: Nat, +y: Nat,
  +sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool},
  fr: {S.look(part, T.Pos{x, y}) == None{} : Maybe<&2, Bool>}) ->
  {List.get(&2, Maybe<&2, Bool>, PL.row_of(Maybe<&2, Bool>, part, y), x) == Some{None{}} : Maybe<&2, Maybe<&2, Bool>>}:
  +xw = P.and_true_l(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +yh = P.and_true_r(Nat.is_lt(x, w), Nat.is_lt(y, h), on)
  +row = PL.row_of(Maybe<&2, Bool>, part, y)
  +xl = {%Equal.sym(Nat, List.length(&2, Maybe<&2, Bool>, row), w, PL.row_in_len(Maybe<&2, Bool>, w, h, part, y, sh, yh)) :
    {Nat.is_lt(x, _) == True{} : Bool};
    xw : {Nat.is_lt(x, List.length(&2, Maybe<&2, Bool>, row)) == True{} : Bool}}
  %fr : {List.get(&2, Maybe<&2, Bool>, row, x) == Some{_} : Maybe<&2, Maybe<&2, Bool>>}
  PL.get_in(Maybe<&2, Bool>, row, x, None{}, xl)

def row_get(+w: Nat, +h: Nat, +part: T.Grid(Maybe<&2, Bool>), +x: Nat, +y: Nat,
  +sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}) ->
  {List.get(&2, List<&2, Maybe<&2, Bool>>, part, y) == Some{PL.row_of(Maybe<&2, Bool>, part, y)} : Maybe<&2, List<&2, Maybe<&2, Bool>>>}:
  PL.row_in_get(Maybe<&2, Bool>, w, h, part, y, sh, P.and_true_r(Nat.is_lt(x, w), Nat.is_lt(y, h), on))

# Assigning an unassigned cell of the board uses up one unassigned cell...
law none_set:
  for +w: Nat
  for +h: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +x: Nat
  for +y: Nat
  for +b: Bool
  for +sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  for +fr: {S.look(part, T.Pos{x, y}) == None{} : Maybe<&2, Bool>}
  {S.part_none(part) == 1n+S.part_none(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{b})) : Nat}

def none_set(w, h, part, x, y, b, sh, on, fr):
  +row = PL.row_of(Maybe<&2, Bool>, part, y)
  none_go(part, y, row, List.set(&2, Maybe<&2, Bool>, row, x, Some{b}), row_get(w, h, part, x, y, sh, on),
    row_none_set(row, x, b, cell_none(w, h, part, x, y, sh, on, fr)))

# ... and adds a mine when it places one ...
law true_set_t:
  for +w: Nat
  for +h: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +x: Nat
  for +y: Nat
  for +sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  for +fr: {S.look(part, T.Pos{x, y}) == None{} : Maybe<&2, Bool>}
  {S.part_true(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}})) == 1n+S.part_true(part) : Nat}

def true_set_t(w, h, part, x, y, sh, on, fr):
  +row = PL.row_of(Maybe<&2, Bool>, part, y)
  true_go_t(part, y, row, List.set(&2, Maybe<&2, Bool>, row, x, Some{True{}}), row_get(w, h, part, x, y, sh, on),
    row_true_set_t(row, x, cell_none(w, h, part, x, y, sh, on, fr)))

# ... and none otherwise.
law true_set_f:
  for +w: Nat
  for +h: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +x: Nat
  for +y: Nat
  for +sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}
  for +fr: {S.look(part, T.Pos{x, y}) == None{} : Maybe<&2, Bool>}
  {S.part_true(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}})) == S.part_true(part) : Nat}

def true_set_f(w, h, part, x, y, sh, on, fr):
  +row = PL.row_of(Maybe<&2, Bool>, part, y)
  true_go_f(part, y, row, List.set(&2, Maybe<&2, Bool>, row, x, Some{False{}}), row_get(w, h, part, x, y, sh, on),
    row_true_set_f(row, x, cell_none(w, h, part, x, y, sh, on, fr)))

# Lists of todos
# ==============

# Every todo of ts passes f (with e for f's context).
def tall(~E: Data, ~f: E -> S.Todo -> Bool, +e: E, ts: List<&2, S.Todo>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      f(e, t) && tall(~E, ~f, e, rest)

def tall_head(~E: Data, ~f: E -> S.Todo -> Bool, +e: E, +t: S.Todo, +rest: List<&2, S.Todo>,
  h: {tall(~E, ~f, e, t <> rest) == True{} : Bool}) -> {f(e, t) == True{} : Bool}:
  P.and_true_l(f(e, t), tall(~E, ~f, e, rest), h)

def tall_tail(~E: Data, ~f: E -> S.Todo -> Bool, +e: E, +t: S.Todo, +rest: List<&2, S.Todo>,
  h: {tall(~E, ~f, e, t <> rest) == True{} : Bool}) -> {tall(~E, ~f, e, rest) == True{} : Bool}:
  P.and_true_r(f(e, t), tall(~E, ~f, e, rest), h)

def tall_cons(~E: Data, ~f: E -> S.Todo -> Bool, +e: E, +t: S.Todo, +rest: List<&2, S.Todo>,
  a: {f(e, t) == True{} : Bool}, b: {tall(~E, ~f, e, rest) == True{} : Bool}) ->
  {tall(~E, ~f, e, t <> rest) == True{} : Bool}:
  %Equal.sym(Bool, tall(~E, ~f, e, rest), True{}, b) : {Bool.and(f(e, t), _) == True{} : Bool}
  %Equal.sym(Bool, f(e, t), True{}, a) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def tall_put(~E: Data, ~f: E -> S.Todo -> Bool, +e: E, +b: Bool, +t: S.Todo, +rest: List<&2, S.Todo>,
  a: {f(e, t) == True{} : Bool}, r: {tall(~E, ~f, e, rest) == True{} : Bool}) ->
  {tall(~E, ~f, e, List.filter.put(S.Todo, t, rest, b)) == True{} : Bool}:
  match b:
    case False{}:
      r
    case True{}:
      tall_cons(~E, ~f, e, t, rest, a, r)

law tall_append:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +xs: List<&2, S.Todo>
  for +ys: List<&2, S.Todo>
  for +a: {tall(~E, ~f, e, xs) == True{} : Bool}
  for b: {tall(~E, ~f, e, ys) == True{} : Bool}
  {tall(~E, ~f, e, List.append(&2, S.Todo, xs, ys)) == True{} : Bool}

def tall_append(E, f, e, xs, ys, a, b):
  match xs:
    case Nil{}:
      b
    case t <> rest:
      tall_cons(~E, ~f, e, t, List.append(&2, S.Todo, rest, ys), tall_head(~E, ~f, e, t, rest, a),
        tall_append(~E, ~f, e, rest, ys, tall_tail(~E, ~f, e, t, rest, a), b))

law tall_nears:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +ts: List<&2, S.Todo>
  for +a: {tall(~E, ~f, e, ts) == True{} : Bool}
  {tall(~E, ~f, e, S.nears(ts)) == True{} : Bool}

def tall_nears(E, f, e, ts, a):
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      tall_put(~E, ~f, e, S.has_rel(t), t, S.nears(rest), tall_head(~E, ~f, e, t, rest, a),
        tall_nears(~E, ~f, e, rest, tall_tail(~E, ~f, e, t, rest, a)))

law tall_fars:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +ts: List<&2, S.Todo>
  for +a: {tall(~E, ~f, e, ts) == True{} : Bool}
  {tall(~E, ~f, e, S.fars(ts)) == True{} : Bool}

def tall_fars(E, f, e, ts, a):
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      tall_put(~E, ~f, e, Bool.not(S.has_rel(t)), t, S.fars(rest), tall_head(~E, ~f, e, t, rest, a),
        tall_fars(~E, ~f, e, rest, tall_tail(~E, ~f, e, t, rest, a)))

law tall_with_c:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +ts: List<&2, S.Todo>
  for +q: T.Pos
  for +a: {tall(~E, ~f, e, ts) == True{} : Bool}
  {tall(~E, ~f, e, S.with_c(ts, q)) == True{} : Bool}

def tall_with_c(E, f, e, ts, q, a):
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      tall_put(~E, ~f, e, B.same(S.todo_c(t), q), t, S.with_c(rest, q), tall_head(~E, ~f, e, t, rest, a),
        tall_with_c(~E, ~f, e, rest, q, tall_tail(~E, ~f, e, t, rest, a)))

law tall_gather:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +qs: List<&2, T.Pos>
  for +ts: List<&2, S.Todo>
  for +a: {tall(~E, ~f, e, ts) == True{} : Bool}
  {tall(~E, ~f, e, S.gather(qs, ts)) == True{} : Bool}

def tall_gather(E, f, e, qs, ts, a):
  match qs:
    case Nil{}:
      {==}
    case q <> t:
      tall_append(~E, ~f, e, S.with_c(ts, q), S.gather(t, ts), tall_with_c(~E, ~f, e, ts, q, a),
        tall_gather(~E, ~f, e, t, ts, a))

law tall_drop:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +ts: List<&2, S.Todo>
  for +k: Nat
  for +a: {tall(~E, ~f, e, ts) == True{} : Bool}
  {tall(~E, ~f, e, List.drop(&2, S.Todo, ts, k)) == True{} : Bool}

def tall_drop(E, f, e, ts, k, a):
  match ts k:
    case Nil{} _:
      {==}
    case t <> rest 0n:
      a
    case t <> rest 1n+j:
      tall_drop(~E, ~f, e, rest, j, tall_tail(~E, ~f, e, t, rest, a))

law tall_take:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +ts: List<&2, S.Todo>
  for +k: Nat
  for +a: {tall(~E, ~f, e, ts) == True{} : Bool}
  {tall(~E, ~f, e, List.take(&2, S.Todo, ts, k)) == True{} : Bool}

def tall_take(E, f, e, ts, k, a):
  match ts k:
    case Nil{} _:
      {==}
    case t <> rest 0n:
      {==}
    case t <> rest 1n+j:
      tall_cons(~E, ~f, e, t, List.take(&2, S.Todo, rest, j), tall_head(~E, ~f, e, t, rest, a),
        tall_take(~E, ~f, e, rest, j, tall_tail(~E, ~f, e, t, rest, a)))

# The order of every search passes whatever the cells of a solve pass.
law tall_plan:
  for ~E: Data
  for ~f: E -> S.Todo -> Bool
  for +e: E
  for +ts: List<&2, S.Todo>
  for +qs: List<&2, T.Pos>
  for +k: Nat
  for +a: {tall(~E, ~f, e, ts) == True{} : Bool}
  {tall(~E, ~f, e, List.append(&2, S.Todo, S.gather(qs, S.nears(ts)),
    List.append(&2, S.Todo, S.rot(S.fars(ts), k), S.order(ts)))) == True{} : Bool}

def tall_plan(E, f, e, ts, qs, k, a):
  +an = tall_nears(~E, ~f, e, ts, a)
  +af = tall_fars(~E, ~f, e, ts, a)
  +far = S.fars(ts)
  tall_append(~E, ~f, e, S.gather(qs, S.nears(ts)), List.append(&2, S.Todo, S.rot(far, k), S.order(ts)),
    tall_gather(~E, ~f, e, qs, S.nears(ts), an),
    tall_append(~E, ~f, e, S.rot(far, k), S.order(ts),
      tall_append(~E, ~f, e, List.drop(&2, S.Todo, far, k), List.take(&2, S.Todo, far, k),
        tall_drop(~E, ~f, e, far, k, af), tall_take(~E, ~f, e, far, k, af)),
      tall_append(~E, ~f, e, S.nears(ts), far, an, af)))

# Todos on the board
# ==================

def con_f(e: PS.WH, t: S.Todo) -> Bool:
  match t:
    case S.Todo{c, rel}:
      PS.onb(e, c)

# The todos of cells on the board are on the board.
law con_todos:
  for +w: Nat
  for +h: Nat
  for +its: List<&2, S.Item>
  for +cs: List<&2, T.Pos>
  for +on: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, cs) == True{} : Bool}
  {tall(~PS.WH, ~con_f, PS.WH{w, h}, S.todos(its, cs)) == True{} : Bool}

def con_todos(w, h, its, cs, on):
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      tall_cons(~PS.WH, ~con_f, PS.WH{w, h}, S.Todo{c, S.around(its, c)}, S.todos(its, t),
        PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, c, t, on),
        con_todos(w, h, its, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, c, t, on)))

# The counting search
# ===================

def none_of(m: Maybe<&2, Bool>, e: {S.is_none(m) == True{} : Bool}) -> {m == None{} : Maybe<&2, Bool>}:
  match m:
    case Some{b}:
      Empty.absurd({Some{b} == None{} : Maybe<&2, Bool>}, P.false_ne_true(e))
    case None{}:
      {==}

def one_less(+a: Nat, +b: Nat, +f: Nat, e1: {a == f : Nat}, e2: {a == 1n+b : Nat}) -> {b == Nat.sub(f, 1n) : Nat}:
  %e1 : {b == Nat.sub(_, 1n) : Nat}
  %Equal.sym(Nat, a, 1n+b, e2) : {b == Nat.sub(_, 1n) : Nat}
  Equal.sym(Nat, Nat.sub(b, 0n), b, P.sub_zero(b))

def when_or_eq(+g0a: Bool, +g0b: Bool, eg0: {g0a == g0b : Bool},
  +d0a: Maybe<&2, T.Grid(Bool)>, +d0b: Maybe<&2, T.Grid(Bool)>, ed0: {d0a == d0b : Maybe<&2, T.Grid(Bool)>},
  +g1a: Bool, +g1b: Bool, eg1: {g1a == g1b : Bool},
  +d1a: Maybe<&2, T.Grid(Bool)>, +d1b: Maybe<&2, T.Grid(Bool)>, ed1: {d1a == d1b : Maybe<&2, T.Grid(Bool)>}) ->
  {S.dfs.or(S.dfs.when(g0a, x => d0a), y => S.dfs.when(g1a, z => d1a))
    == S.dfs.or(S.dfs.when(g0b, x => d0b), y => S.dfs.when(g1b, z => d1b)) : Maybe<&2, T.Grid(Bool)>}:
  %eg0 : {S.dfs.or(S.dfs.when(g0a, x => d0a), y => S.dfs.when(g1a, z => d1a))
    == S.dfs.or(S.dfs.when(_, x => d0b), y => S.dfs.when(g1b, z => d1b)) : Maybe<&2, T.Grid(Bool)>}
  %ed0 : {S.dfs.or(S.dfs.when(g0a, x => d0a), y => S.dfs.when(g1a, z => d1a))
    == S.dfs.or(S.dfs.when(g0a, x => _), y => S.dfs.when(g1b, z => d1b)) : Maybe<&2, T.Grid(Bool)>}
  %eg1 : {S.dfs.or(S.dfs.when(g0a, x => d0a), y => S.dfs.when(g1a, z => d1a))
    == S.dfs.or(S.dfs.when(g0a, x => d0a), y => S.dfs.when(_, z => d1b)) : Maybe<&2, T.Grid(Bool)>}
  %ed1 : {S.dfs.or(S.dfs.when(g0a, x => d0a), y => S.dfs.when(g1a, z => d1a))
    == S.dfs.or(S.dfs.when(g0a, x => d0a), y => S.dfs.when(g1a, z => _)) : Maybe<&2, T.Grid(Bool)>}
  {==}

def dfs2_eq.node(+x: Nat, +y: Nat, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +its: List<&2, S.Item>, +t: Nat, +f: Nat,
  +sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, +on: {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool},
  +et: {S.part_true(part) == t : Nat}, +ef: {S.part_none(part) == f : Nat},
  +fr: Bool, fre: {S.is_none(S.look(part, T.Pos{x, y})) == fr : Bool},
  ks: {S.dfs2(rest, part, t, f, S.Ctx{w, h, n, rows, its}) == S.dfs(rest, part, S.Ctx{w, h, n, rows, its}) : Maybe<&2, T.Grid(Bool)>},
  k0: {S.part_true(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}})) == t : Nat} ->
    {S.part_none(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}})) == Nat.sub(f, 1n) : Nat} ->
    {S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}}), t, Nat.sub(f, 1n), S.Ctx{w, h, n, rows, its})
      == S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}}), S.Ctx{w, h, n, rows, its}) : Maybe<&2, T.Grid(Bool)>},
  k1: {S.part_true(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}})) == 1n+t : Nat} ->
    {S.part_none(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}})) == Nat.sub(f, 1n) : Nat} ->
    {S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}}), 1n+t, Nat.sub(f, 1n), S.Ctx{w, h, n, rows, its})
      == S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}}), S.Ctx{w, h, n, rows, its}) : Maybe<&2, T.Grid(Bool)>}) ->
  {S.dfs.free(fr, u => S.dfs2(rest, part, t, f, S.Ctx{w, h, n, rows, its}),
      v => S.dfs.or(S.dfs.when(Bool.and(S.between(t, Nat.sub(f, 1n), n),
          S.items_open(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}}), rel)),
        x0 => S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}}), t, Nat.sub(f, 1n), S.Ctx{w, h, n, rows, its})),
      y0 => S.dfs.when(Bool.and(S.between(1n+t, Nat.sub(f, 1n), n),
          S.items_open(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}}), rel)),
        z0 => S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}}), 1n+t, Nat.sub(f, 1n), S.Ctx{w, h, n, rows, its}))))
    == S.dfs.free(fr, u => S.dfs(rest, part, S.Ctx{w, h, n, rows, its}),
      v => S.dfs.or(S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}}), rel, n),
        x0 => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{False{}}), S.Ctx{w, h, n, rows, its})),
      y0 => S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}}), rel, n),
        z0 => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, T.Pos{x, y}, Some{True{}}), S.Ctx{w, h, n, rows, its})))) : Maybe<&2, T.Grid(Bool)>}:
  match fr:
    case False{}:
      ks
    case True{}:
      +q = {T.Pos{x, y} : T.Pos}
      +p0 = B.set_at(Maybe<&2, Bool>, part, q, Some{False{}})
      +p1 = B.set_at(Maybe<&2, Bool>, part, q, Some{True{}})
      +lk = none_of(S.look(part, q), fre)
      +e0f = one_less(S.part_none(part), S.part_none(p0), f, ef, none_set(w, h, part, x, y, False{}, sh, on, lk))
      +e1f = one_less(S.part_none(part), S.part_none(p1), f, ef, none_set(w, h, part, x, y, True{}, sh, on, lk))
      +e0t = Equal.trans(Nat, S.part_true(p0), S.part_true(part), t, true_set_f(w, h, part, x, y, sh, on, lk), et)
      +e1t = {%et : {S.part_true(p1) == 1n+_ : Nat}; true_set_t(w, h, part, x, y, sh, on, lk) : {S.part_true(p1) == 1n+t : Nat}}
      +eg0 = {%e0t : {Bool.and(S.between(_, Nat.sub(f, 1n), n), S.items_open(p0, rel)) == S.open_ok(p0, rel, n) : Bool};
        %e0f : {Bool.and(S.between(S.part_true(p0), _, n), S.items_open(p0, rel)) == S.open_ok(p0, rel, n) : Bool};
        {==} : {Bool.and(S.between(t, Nat.sub(f, 1n), n), S.items_open(p0, rel)) == S.open_ok(p0, rel, n) : Bool}}
      +eg1 = {%e1t : {Bool.and(S.between(_, Nat.sub(f, 1n), n), S.items_open(p1, rel)) == S.open_ok(p1, rel, n) : Bool};
        %e1f : {Bool.and(S.between(S.part_true(p1), _, n), S.items_open(p1, rel)) == S.open_ok(p1, rel, n) : Bool};
        {==} : {Bool.and(S.between(1n+t, Nat.sub(f, 1n), n), S.items_open(p1, rel)) == S.open_ok(p1, rel, n) : Bool}}
      +ctx = {S.Ctx{w, h, n, rows, its} : S.Ctx}
      when_or_eq(Bool.and(S.between(t, Nat.sub(f, 1n), n), S.items_open(p0, rel)), S.open_ok(p0, rel, n), eg0,
        S.dfs2(rest, p0, t, Nat.sub(f, 1n), ctx), S.dfs(rest, p0, ctx), k0(e0t, e0f),
        Bool.and(S.between(1n+t, Nat.sub(f, 1n), n), S.items_open(p1, rel)), S.open_ok(p1, rel, n), eg1,
        S.dfs2(rest, p1, 1n+t, Nat.sub(f, 1n), ctx), S.dfs(rest, p1, ctx), k1(e1t, e1f))

# With the counts right and every cell on the board, the counting search
# answers exactly as the plain one.
law dfs2_eq:
  for +todo: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +its: List<&2, S.Item>
  for +t: Nat
  for +f: Nat
  for +sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +con: {tall(~PS.WH, ~con_f, PS.WH{w, h}, todo) == True{} : Bool}
  for +et: {S.part_true(part) == t : Nat}
  for +ef: {S.part_none(part) == f : Nat}
  {S.dfs2(todo, part, t, f, S.Ctx{w, h, n, rows, its}) == S.dfs(todo, part, S.Ctx{w, h, n, rows, its}) : Maybe<&2, T.Grid(Bool)>}

def dfs2_eq(todo, part, w, h, n, rows, its, t, f, sh, con, et, ef):
  match todo:
    case Nil{}:
      {==}
    case S.Todo{c, rel} <> rest:
      match c:
        case T.Pos{x, y}:
          +q = {T.Pos{x, y} : T.Pos}
          +onc = tall_head(~PS.WH, ~con_f, PS.WH{w, h}, S.Todo{q, rel}, rest, con)
          +conr = tall_tail(~PS.WH, ~con_f, PS.WH{w, h}, S.Todo{q, rel}, rest, con)
          +p0 = B.set_at(Maybe<&2, Bool>, part, q, Some{False{}})
          +p1 = B.set_at(Maybe<&2, Bool>, part, q, Some{True{}})
          dfs2_eq.node(x, y, rel, rest, part, w, h, n, rows, its, t, f, sh, onc, et, ef, S.is_none(S.look(part, q)), {==},
            dfs2_eq(rest, part, w, h, n, rows, its, t, f, sh, conr, et, ef),
            e0t => e0f => dfs2_eq(rest, p0, w, h, n, rows, its, t, Nat.sub(f, 1n),
              PL.shaped_set(Maybe<&2, Bool>, w, h, part, q, Some{False{}}, sh), conr, e0t, e0f),
            e1t => e1f => dfs2_eq(rest, p1, w, h, n, rows, its, 1n+t, Nat.sub(f, 1n),
              PL.shaped_set(Maybe<&2, Bool>, w, h, part, q, Some{True{}}, sh), conr, e1t, e1f))
