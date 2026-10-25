import Base
import ./types.bend as T
import ./board.bend as B
import ./solver.bend as S
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG
import ./proof_copy.bend as PC
import ./proof_lists.bend as PL
import ./proof_cells.bend as PS
import ./proof_sums.bend as PU
import ./proof_walk.bend as PW
import ./proof_speed.bend as PF

# The solver is right: when it names a cell, the cell is provably safe;
# when it names none, every hidden cell might hold a mine.

# Counting as sums
# ================

def one(b: Bool) -> Nat:
  Bool.pick(Nat, b, 1n, 0n)

def tf(m: Maybe<&2, Bool>) -> Nat:
  S.one_if(S.is_true(m))

def nf(m: Maybe<&2, Bool>) -> Nat:
  S.one_if(S.is_none(m))

law row_mines_sum:
  for +r: List<&2, Bool>
  {B.row_mines(r) == PU.rsum(~Bool, ~one, r) : Nat}

def row_mines_sum(r):
  match r:
    case Nil{}:
      {==}
    case b <> t:
      %row_mines_sum(t) : {Nat.add(Bool.pick(Nat, b, 1n, 0n), B.row_mines(t)) == Nat.add(one(b), _) : Nat}
      {==}

law total_sum:
  for +g: T.Grid(Bool)
  {B.total_mines(g) == PU.gsum(~Bool, ~one, g) : Nat}

def total_sum(g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %row_mines_sum(r) : {Nat.add(B.row_mines(r), B.total_mines(t)) == Nat.add(_, PU.gsum(~Bool, ~one, t)) : Nat}
      %total_sum(t) : {Nat.add(B.row_mines(r), B.total_mines(t)) == Nat.add(B.row_mines(r), _) : Nat}
      {==}

law count_sum:
  for +layout: T.Grid(Bool)
  for +ps: List<&2, T.Pos>
  {B.count_mines(layout, ps) == PU.csum(~Bool, ~one, False{}, layout, ps) : Nat}

def count_sum(layout, ps):
  match ps:
    case Nil{}:
      {==}
    case q <> t:
      %count_sum(layout, t) :
        {Nat.add(Bool.pick(Nat, B.mine(layout, q), 1n, 0n), B.count_mines(layout, t))
          == Nat.add(one(B.at(Bool, False{}, layout, q)), _) : Nat}
      {==}

law row_true_sum:
  for +r: List<&2, Maybe<&2, Bool>>
  {S.row_true(r) == PU.rsum(~Maybe<&2, Bool>, ~tf, r) : Nat}

def row_true_sum(r):
  match r:
    case Nil{}:
      {==}
    case m <> t:
      %row_true_sum(t) : {Nat.add(S.one_if(S.is_true(m)), S.row_true(t)) == Nat.add(tf(m), _) : Nat}
      {==}

law row_none_sum:
  for +r: List<&2, Maybe<&2, Bool>>
  {S.row_none(r) == PU.rsum(~Maybe<&2, Bool>, ~nf, r) : Nat}

def row_none_sum(r):
  match r:
    case Nil{}:
      {==}
    case m <> t:
      %row_none_sum(t) : {Nat.add(S.one_if(S.is_none(m)), S.row_none(t)) == Nat.add(nf(m), _) : Nat}
      {==}

law part_true_sum:
  for +g: T.Grid(Maybe<&2, Bool>)
  {S.part_true(g) == PU.gsum(~Maybe<&2, Bool>, ~tf, g) : Nat}

def part_true_sum(g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %row_true_sum(r) : {Nat.add(S.row_true(r), S.part_true(t)) == Nat.add(_, PU.gsum(~Maybe<&2, Bool>, ~tf, t)) : Nat}
      %part_true_sum(t) : {Nat.add(S.row_true(r), S.part_true(t)) == Nat.add(S.row_true(r), _) : Nat}
      {==}

law part_none_sum:
  for +g: T.Grid(Maybe<&2, Bool>)
  {S.part_none(g) == PU.gsum(~Maybe<&2, Bool>, ~nf, g) : Nat}

def part_none_sum(g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %row_none_sum(r) : {Nat.add(S.row_none(r), S.part_none(t)) == Nat.add(_, PU.gsum(~Maybe<&2, Bool>, ~nf, t)) : Nat}
      %part_none_sum(t) : {Nat.add(S.row_none(r), S.part_none(t)) == Nat.add(S.row_none(r), _) : Nat}
      {==}

law true_among_sum:
  for +part: T.Grid(Maybe<&2, Bool>)
  for +ps: List<&2, T.Pos>
  {S.true_among(part, ps) == PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ps) : Nat}

def true_among_sum(part, ps):
  match ps:
    case Nil{}:
      {==}
    case q <> t:
      %true_among_sum(part, t) :
        {Nat.add(S.one_if(S.is_true(S.look(part, q))), S.true_among(part, t))
          == Nat.add(tf(B.at(Maybe<&2, Bool>, None{}, part, q)), _) : Nat}
      {==}

law none_among_sum:
  for +part: T.Grid(Maybe<&2, Bool>)
  for +ps: List<&2, T.Pos>
  {S.none_among(part, ps) == PU.csum(~Maybe<&2, Bool>, ~nf, None{}, part, ps) : Nat}

def none_among_sum(part, ps):
  match ps:
    case Nil{}:
      {==}
    case q <> t:
      %none_among_sum(part, t) :
        {Nat.add(S.one_if(S.is_none(S.look(part, q))), S.none_among(part, t))
          == Nat.add(nf(B.at(Maybe<&2, Bool>, None{}, part, q)), _) : Nat}
      {==}

# A full layout completing a partial one
# ======================================

def beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

law beq_sound:
  for +a: Bool
  for +b: Bool
  for e: {beq(a, b) == True{} : Bool}
  {a == b : Bool}

def beq_sound(a, b, e):
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(e))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, P.false_ne_true(e))

law beq_refl:
  for +a: Bool
  {beq(a, a) == True{} : Bool}

def beq_refl(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cmp_cell(m: Maybe<&2, Bool>, b: Bool) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{c}:
      beq(b, c)

type CE is Data:
  CE{part: T.Grid(Maybe<&2, Bool>), layout: T.Grid(Bool)}

def cmp_f.go(e: CE, +q: T.Pos) -> Bool:
  match e:
    case CE{part, layout}:
      cmp_cell(S.look(part, q), B.mine(layout, q))

def cmp_f(e: CE, q: T.Pos) -> Bool:
  cmp_f.go(e, q)

# The layout has every cell the partial layout fixes.
def completes(+w: Nat, +h: Nat, part: T.Grid(Maybe<&2, Bool>), layout: T.Grid(Bool)) -> Bool:
  PS.allp(~CE, ~cmp_f, CE{part, layout}, B.cells(w, h))

law comp_cell:
  for +w: Nat
  for +h: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +layout: T.Grid(Bool)
  for comp: {completes(w, h, part, layout) == True{} : Bool}
  for +q: T.Pos
  for on: {B.on_board(w, h, q) == True{} : Bool}
  {cmp_cell(S.look(part, q), B.mine(layout, q)) == True{} : Bool}

def comp_cell(w, h, part, layout, comp, q, on):
  PS.allp_member(~CE, ~cmp_f, CE{part, layout}, B.cells(w, h), q, comp, PS.cells_member(w, h, q, on))

law cell_lo:
  for +m: Maybe<&2, Bool>
  for +b: Bool
  for c: {cmp_cell(m, b) == True{} : Bool}
  {Nat.is_le(tf(m), one(b)) == True{} : Bool}

def cell_lo(m, b, c):
  match m:
    case None{}:
      P.le_zero_l(one(b))
    case Some{c0}:
      %Equal.sym(Bool, b, c0, beq_sound(b, c0, c)) : {Nat.is_le(S.one_if(c0), one(_)) == True{} : Bool}
      P.le_refl(one(c0))

law cell_hi:
  for +m: Maybe<&2, Bool>
  for +b: Bool
  for c: {cmp_cell(m, b) == True{} : Bool}
  {Nat.is_le(one(b), Nat.add(tf(m), nf(m))) == True{} : Bool}

def cell_hi(m, b, c):
  match m:
    case None{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Some{c0}:
      %Equal.sym(Bool, b, c0, beq_sound(b, c0, c)) : {Nat.is_le(one(_), Nat.add(S.one_if(c0), 0n)) == True{} : Bool}
      P.le_of_add(one(c0), 0n)

law among_lo:
  for +w: Nat
  for +h: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +layout: T.Grid(Bool)
  for +comp: {completes(w, h, part, layout) == True{} : Bool}
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  {Nat.is_le(PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ps), PU.csum(~Bool, ~one, False{}, layout, ps)) == True{} : Bool}

def among_lo(w, h, part, layout, comp, ps, ons):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +m = S.look(part, q)
      +b = B.mine(layout, q)
      P.le_add(tf(m), one(b), PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, t), PU.csum(~Bool, ~one, False{}, layout, t),
        cell_lo(m, b, comp_cell(w, h, part, layout, comp, q, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))),
        among_lo(w, h, part, layout, comp, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons)))

law among_hi:
  for +w: Nat
  for +h: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +layout: T.Grid(Bool)
  for +comp: {completes(w, h, part, layout) == True{} : Bool}
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  {Nat.is_le(PU.csum(~Bool, ~one, False{}, layout, ps),
    Nat.add(PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ps), PU.csum(~Maybe<&2, Bool>, ~nf, None{}, part, ps))) == True{} : Bool}

def among_hi(w, h, part, layout, comp, ps, ons):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +m = S.look(part, q)
      +b = B.mine(layout, q)
      +tt = PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, t)
      +nt = PU.csum(~Maybe<&2, Bool>, ~nf, None{}, part, t)
      %Equal.sym(Nat, Nat.add(Nat.add(tf(m), tt), Nat.add(nf(m), nt)), Nat.add(Nat.add(tf(m), nf(m)), Nat.add(tt, nt)),
        P.add_swap(tf(m), tt, nf(m), nt)) :
        {Nat.is_le(Nat.add(one(b), PU.csum(~Bool, ~one, False{}, layout, t)), _) == True{} : Bool}
      P.le_add(one(b), Nat.add(tf(m), nf(m)), PU.csum(~Bool, ~one, False{}, layout, t), Nat.add(tt, nt),
        cell_hi(m, b, comp_cell(w, h, part, layout, comp, q, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))),
        among_hi(w, h, part, layout, comp, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons)))

# Pruning only drops partial layouts that no consistent layout completes
# ======================================================================

def item_onb(e: PS.WH, i: S.Item) -> Bool:
  match e i:
    case PS.WH{+w, +h} S.Item{p, s, ns}:
      B.on_board(w, h, p) && PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ns)

# Every revealed cell of the items, and every cell its number counts, is on the board.
def items_onb(+e: PS.WH, its: List<&2, S.Item>) -> Bool:
  match its:
    case Nil{}:
      True{}
    case i <> t:
      item_onb(e, i) && items_onb(e, t)

def sum_eq_cells(~A: Data, ~f: A -> Nat, +d: A, +w: Nat, +h: Nat, +g: T.Grid(A), +x: Nat,
  sh: {B.shaped(A, w, h, g) == True{} : Bool}, e: {x == PU.gsum(~A, ~f, g) : Nat}) ->
  {x == PU.csum(~A, ~f, d, g, B.cells(w, h)) : Nat}:
  Equal.trans(Nat, x, PU.gsum(~A, ~f, g), PU.csum(~A, ~f, d, g, B.cells(w, h)), e,
    Equal.sym(Nat, PU.csum(~A, ~f, d, g, B.cells(w, h)), PU.gsum(~A, ~f, g), PU.grid_sum(~A, ~f, d, w, h, g, sh)))

def item_open_sound(+w: Nat, +h: Nat, +part: T.Grid(Maybe<&2, Bool>), +layout: T.Grid(Bool),
  +comp: {completes(w, h, part, layout) == True{} : Bool}, +p: T.Pos, +s: T.Seen, +ns: List<&2, T.Pos>,
  ok: {S.item_ok(s, p, ns, layout) == True{} : Bool},
  +on: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ns) == True{} : Bool}) ->
  {S.item_open(s, part, ns) == True{} : Bool}:
  match s:
    case T.Shown{k}:
      +c = B.count_mines(layout, ns)
      +ck = P.eq_sound(c, k, P.and_true_r(Bool.not(B.mine(layout, p)), Nat.is_eq(c, k), ok))
      %ck : {S.between(S.true_among(part, ns), S.none_among(part, ns), _) == True{} : Bool}
      %Equal.sym(Nat, S.true_among(part, ns), PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ns), true_among_sum(part, ns)) :
        {S.between(_, S.none_among(part, ns), c) == True{} : Bool}
      %Equal.sym(Nat, S.none_among(part, ns), PU.csum(~Maybe<&2, Bool>, ~nf, None{}, part, ns), none_among_sum(part, ns)) :
        {S.between(PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ns), _, c) == True{} : Bool}
      %Equal.sym(Nat, c, PU.csum(~Bool, ~one, False{}, layout, ns), count_sum(layout, ns)) :
        {S.between(PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ns), PU.csum(~Maybe<&2, Bool>, ~nf, None{}, part, ns), _)
          == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ns), PU.csum(~Bool, ~one, False{}, layout, ns)),
        True{}, among_lo(w, h, part, layout, comp, ns, on)) :
        {Bool.and(_, Nat.is_le(PU.csum(~Bool, ~one, False{}, layout, ns),
          Nat.add(PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, ns), PU.csum(~Maybe<&2, Bool>, ~nf, None{}, part, ns)))) == True{} : Bool}
      among_hi(w, h, part, layout, comp, ns, on)
    case T.Hidden{}:
      {==}
    case T.Boom{}:
      {==}

law items_open_sound:
  for +w: Nat
  for +h: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +layout: T.Grid(Bool)
  for +comp: {completes(w, h, part, layout) == True{} : Bool}
  for +rel: List<&2, S.Item>
  for +rok: {S.items_ok(rel, layout) == True{} : Bool}
  for +ron: {items_onb(PS.WH{w, h}, rel) == True{} : Bool}
  {S.items_open(part, rel) == True{} : Bool}

def items_open_sound(w, h, part, layout, comp, rel, rok, ron):
  match rel:
    case Nil{}:
      {==}
    case S.Item{p, s, ns} <> t:
      +i = {S.Item{p, s, ns} : S.Item}
      +io = item_onb(PS.WH{w, h}, i)
      +ok1 = S.item_ok(s, p, ns, layout)
      %Equal.sym(Bool, S.item_open(s, part, ns), True{},
        item_open_sound(w, h, part, layout, comp, p, s, ns, P.and_true_l(ok1, S.items_ok(t, layout), rok),
          P.and_true_r(B.on_board(w, h, p), PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ns),
            P.and_true_l(io, items_onb(PS.WH{w, h}, t), ron)))) :
        {Bool.and(_, S.items_open(part, t)) == True{} : Bool}
      items_open_sound(w, h, part, layout, comp, t, P.and_true_r(ok1, S.items_ok(t, layout), rok),
        P.and_true_r(io, items_onb(PS.WH{w, h}, t), ron))

# A partial layout that a consistent layout completes is never pruned.
law open_ok_sound:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +part: T.Grid(Maybe<&2, Bool>)
  for +rel: List<&2, S.Item>
  for +layout: T.Grid(Bool)
  for +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +shL: {B.shaped(Bool, w, h, layout) == True{} : Bool}
  for +comp: {completes(w, h, part, layout) == True{} : Bool}
  for tot: {B.total_mines(layout) == n : Nat}
  for rok: {S.items_ok(rel, layout) == True{} : Bool}
  for ron: {items_onb(PS.WH{w, h}, rel) == True{} : Bool}
  {S.open_ok(part, rel, n) == True{} : Bool}

def open_ok_sound(w, h, n, part, rel, layout, shP, shL, comp, tot, rok, ron):
  +pt = sum_eq_cells(~Maybe<&2, Bool>, ~tf, None{}, w, h, part, S.part_true(part), shP, part_true_sum(part))
  +pn = sum_eq_cells(~Maybe<&2, Bool>, ~nf, None{}, w, h, part, S.part_none(part), shP, part_none_sum(part))
  +nc = sum_eq_cells(~Bool, ~one, False{}, w, h, layout, n, shL,
    Equal.trans(Nat, n, B.total_mines(layout), PU.gsum(~Bool, ~one, layout), Equal.sym(Nat, B.total_mines(layout), n, tot),
      total_sum(layout)))
  +T0 = PU.csum(~Maybe<&2, Bool>, ~tf, None{}, part, B.cells(w, h))
  +N0 = PU.csum(~Maybe<&2, Bool>, ~nf, None{}, part, B.cells(w, h))
  +C0 = PU.csum(~Bool, ~one, False{}, layout, B.cells(w, h))
  %Equal.sym(Bool, S.items_open(part, rel), True{}, items_open_sound(w, h, part, layout, comp, rel, rok, ron)) :
    {Bool.and(S.between(S.part_true(part), S.part_none(part), n), _) == True{} : Bool}
  %Equal.sym(Nat, S.part_true(part), T0, pt) : {Bool.and(S.between(_, S.part_none(part), n), True{}) == True{} : Bool}
  %Equal.sym(Nat, S.part_none(part), N0, pn) : {Bool.and(S.between(T0, _, n), True{}) == True{} : Bool}
  %Equal.sym(Nat, n, C0, nc) : {Bool.and(S.between(T0, N0, _), True{}) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(T0, C0), True{}, among_lo(w, h, part, layout, comp, B.cells(w, h), PS.cells_on(w, h))) :
    {Bool.and(Bool.and(_, Nat.is_le(C0, Nat.add(T0, N0))), True{}) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(C0, Nat.add(T0, N0)), True{}, among_hi(w, h, part, layout, comp, B.cells(w, h), PS.cells_on(w, h))) :
    {Bool.and(Bool.and(True{}, _), True{}) == True{} : Bool}
  {==}

# Filling in a partial layout
# ===========================

law fill_rows_get:
  for +g: T.Grid(Maybe<&2, Bool>)
  for +y: Nat
  {Maybe.default(&2, List<&2, Bool>, List.get(&2, List<&2, Bool>, S.fill(g), y), Nil{})
    == S.fill.row(Maybe.default(&2, List<&2, Maybe<&2, Bool>>, List.get(&2, List<&2, Maybe<&2, Bool>>, g, y), Nil{}))
    : List<&2, Bool>}

def fill_rows_get(g, y):
  match g y:
    case Nil{} _:
      {==}
    case r <> t 0n:
      {==}
    case r <> t 1n+k:
      fill_rows_get(t, k)

law fill_row_get:
  for +r: List<&2, Maybe<&2, Bool>>
  for +x: Nat
  {Maybe.default(&2, Bool, List.get(&2, Bool, S.fill.row(r), x), False{})
    == Maybe.default(&2, Bool, Maybe.default(&2, Maybe<&2, Bool>, List.get(&2, Maybe<&2, Bool>, r, x), None{}), False{}) : Bool}

def fill_row_get(r, x):
  match r x:
    case Nil{} _:
      {==}
    case m <> t 0n:
      {==}
    case m <> t 1n+k:
      fill_row_get(t, k)

# A filled-in cell holds what the partial layout fixed (False if nothing).
law fill_at:
  for +part: T.Grid(Maybe<&2, Bool>)
  for +q: T.Pos
  {B.mine(S.fill(part), q) == Maybe.default(&2, Bool, S.look(part, q), False{}) : Bool}

def fill_at(part, q):
  match q:
    case T.Pos{x, y}:
      %Equal.sym(List<&2, Bool>, Maybe.default(&2, List<&2, Bool>, List.get(&2, List<&2, Bool>, S.fill(part), y), Nil{}),
        S.fill.row(Maybe.default(&2, List<&2, Maybe<&2, Bool>>, List.get(&2, List<&2, Maybe<&2, Bool>>, part, y), Nil{})),
        fill_rows_get(part, y)) :
        {Maybe.default(&2, Bool, List.get(&2, Bool, _, x), False{})
          == Maybe.default(&2, Bool, S.look(part, T.Pos{x, y}), False{}) : Bool}
      fill_row_get(Maybe.default(&2, List<&2, Maybe<&2, Bool>>, List.get(&2, List<&2, Maybe<&2, Bool>>, part, y), Nil{}), x)

law fill_row_len:
  for +r: List<&2, Maybe<&2, Bool>>
  {List.length(&2, Bool, S.fill.row(r)) == List.length(&2, Maybe<&2, Bool>, r) : Nat}

def fill_row_len(r):
  match r:
    case Nil{}:
      {==}
    case m <> t:
      %Equal.sym(Nat, List.length(&2, Bool, S.fill.row(t)), List.length(&2, Maybe<&2, Bool>, t), fill_row_len(t)) :
        {1n+_ == 1n+List.length(&2, Maybe<&2, Bool>, t) : Nat}
      {==}

law fill_len:
  for +g: T.Grid(Maybe<&2, Bool>)
  {List.length(&2, List<&2, Bool>, S.fill(g)) == List.length(&2, List<&2, Maybe<&2, Bool>>, g) : Nat}

def fill_len(g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %Equal.sym(Nat, List.length(&2, List<&2, Bool>, S.fill(t)), List.length(&2, List<&2, Maybe<&2, Bool>>, t), fill_len(t)) :
        {1n+_ == 1n+List.length(&2, List<&2, Maybe<&2, Bool>>, t) : Nat}
      {==}

law fill_wide:
  for +w: Nat
  for +g: T.Grid(Maybe<&2, Bool>)
  {B.rows_wide(Bool, w, S.fill(g)) == B.rows_wide(Maybe<&2, Bool>, w, g) : Bool}

def fill_wide(w, g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %Equal.sym(Nat, List.length(&2, Bool, S.fill.row(r)), List.length(&2, Maybe<&2, Bool>, r), fill_row_len(r)) :
        {Bool.and(Nat.is_eq(_, w), B.rows_wide(Bool, w, S.fill(t)))
          == Bool.and(Nat.is_eq(List.length(&2, Maybe<&2, Bool>, r), w), B.rows_wide(Maybe<&2, Bool>, w, t)) : Bool}
      %Equal.sym(Bool, B.rows_wide(Bool, w, S.fill(t)), B.rows_wide(Maybe<&2, Bool>, w, t), fill_wide(w, t)) :
        {Bool.and(Nat.is_eq(List.length(&2, Maybe<&2, Bool>, r), w), _)
          == Bool.and(Nat.is_eq(List.length(&2, Maybe<&2, Bool>, r), w), B.rows_wide(Maybe<&2, Bool>, w, t)) : Bool}
      {==}

law fill_shaped:
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(Maybe<&2, Bool>)
  {B.shaped(Bool, w, h, S.fill(g)) == B.shaped(Maybe<&2, Bool>, w, h, g) : Bool}

def fill_shaped(w, h, g):
  %Equal.sym(Nat, List.length(&2, List<&2, Bool>, S.fill(g)), List.length(&2, List<&2, Maybe<&2, Bool>>, g), fill_len(g)) :
    {Bool.and(Nat.is_eq(_, h), B.rows_wide(Bool, w, S.fill(g)))
      == Bool.and(Nat.is_eq(List.length(&2, List<&2, Maybe<&2, Bool>>, g), h), B.rows_wide(Maybe<&2, Bool>, w, g)) : Bool}
  %Equal.sym(Bool, B.rows_wide(Bool, w, S.fill(g)), B.rows_wide(Maybe<&2, Bool>, w, g), fill_wide(w, g)) :
    {Bool.and(Nat.is_eq(List.length(&2, List<&2, Maybe<&2, Bool>>, g), h), _)
      == Bool.and(Nat.is_eq(List.length(&2, List<&2, Maybe<&2, Bool>>, g), h), B.rows_wide(Maybe<&2, Bool>, w, g)) : Bool}
  {==}

# Two layouts that agree cell by cell
# ===================================

type AG is Data:
  AG{l1: T.Grid(Bool), l2: T.Grid(Bool)}

def ag_f.go(e: AG, +q: T.Pos) -> Bool:
  match e:
    case AG{l1, l2}:
      beq(B.mine(l1, q), B.mine(l2, q))

def ag_f(e: AG, q: T.Pos) -> Bool:
  ag_f.go(e, q)

def agree(+w: Nat, +h: Nat, l1: T.Grid(Bool), l2: T.Grid(Bool)) -> Bool:
  PS.allp(~AG, ~ag_f, AG{l1, l2}, B.cells(w, h))

law agree_cell:
  for +w: Nat
  for +h: Nat
  for +l1: T.Grid(Bool)
  for +l2: T.Grid(Bool)
  for ag: {agree(w, h, l1, l2) == True{} : Bool}
  for +q: T.Pos
  for on: {B.on_board(w, h, q) == True{} : Bool}
  {B.mine(l1, q) == B.mine(l2, q) : Bool}

def agree_cell(w, h, l1, l2, ag, q, on):
  beq_sound(B.mine(l1, q), B.mine(l2, q),
    PS.allp_member(~AG, ~ag_f, AG{l1, l2}, B.cells(w, h), q, ag, PS.cells_member(w, h, q, on)))

law count_agree:
  for +w: Nat
  for +h: Nat
  for +l1: T.Grid(Bool)
  for +l2: T.Grid(Bool)
  for +ag: {agree(w, h, l1, l2) == True{} : Bool}
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  {B.count_mines(l1, ps) == B.count_mines(l2, ps) : Nat}

def count_agree(w, h, l1, l2, ag, ps, ons):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      %Equal.sym(Bool, B.mine(l1, q), B.mine(l2, q), agree_cell(w, h, l1, l2, ag, q, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))) :
        {Nat.add(Bool.pick(Nat, _, 1n, 0n), B.count_mines(l1, t)) == Nat.add(Bool.pick(Nat, B.mine(l2, q), 1n, 0n), B.count_mines(l2, t)) : Nat}
      %Equal.sym(Nat, B.count_mines(l1, t), B.count_mines(l2, t),
        count_agree(w, h, l1, l2, ag, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))) :
        {Nat.add(Bool.pick(Nat, B.mine(l2, q), 1n, 0n), _) == Nat.add(Bool.pick(Nat, B.mine(l2, q), 1n, 0n), B.count_mines(l2, t)) : Nat}
      {==}

law total_cells:
  for +w: Nat
  for +h: Nat
  for +l: T.Grid(Bool)
  for sh: {B.shaped(Bool, w, h, l) == True{} : Bool}
  {B.total_mines(l) == B.count_mines(l, B.cells(w, h)) : Nat}

def total_cells(w, h, l, sh):
  Equal.trans(Nat, B.total_mines(l), PU.gsum(~Bool, ~one, l), B.count_mines(l, B.cells(w, h)), total_sum(l),
    Equal.trans(Nat, PU.gsum(~Bool, ~one, l), PU.csum(~Bool, ~one, False{}, l, B.cells(w, h)), B.count_mines(l, B.cells(w, h)),
      Equal.sym(Nat, PU.csum(~Bool, ~one, False{}, l, B.cells(w, h)), PU.gsum(~Bool, ~one, l), PU.grid_sum(~Bool, ~one, False{}, w, h, l, sh)),
      Equal.sym(Nat, B.count_mines(l, B.cells(w, h)), PU.csum(~Bool, ~one, False{}, l, B.cells(w, h)), count_sum(l, B.cells(w, h)))))

law total_agree:
  for +w: Nat
  for +h: Nat
  for +l1: T.Grid(Bool)
  for +l2: T.Grid(Bool)
  for sh1: {B.shaped(Bool, w, h, l1) == True{} : Bool}
  for sh2: {B.shaped(Bool, w, h, l2) == True{} : Bool}
  for +ag: {agree(w, h, l1, l2) == True{} : Bool}
  {B.total_mines(l1) == B.total_mines(l2) : Nat}

def total_agree(w, h, l1, l2, sh1, sh2, ag):
  Equal.trans(Nat, B.total_mines(l1), B.count_mines(l1, B.cells(w, h)), B.total_mines(l2), total_cells(w, h, l1, sh1),
    Equal.trans(Nat, B.count_mines(l1, B.cells(w, h)), B.count_mines(l2, B.cells(w, h)), B.total_mines(l2),
      count_agree(w, h, l1, l2, ag, B.cells(w, h), PS.cells_on(w, h)),
      Equal.sym(Nat, B.total_mines(l2), B.count_mines(l2, B.cells(w, h)), total_cells(w, h, l2, sh2))))

def item_ok_agree(+w: Nat, +h: Nat, +l1: T.Grid(Bool), +l2: T.Grid(Bool), +ag: {agree(w, h, l1, l2) == True{} : Bool},
  +p: T.Pos, +s: T.Seen, +ns: List<&2, T.Pos>, on: {B.on_board(w, h, p) == True{} : Bool},
  ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ns) == True{} : Bool}) ->
  {S.item_ok(s, p, ns, l1) == S.item_ok(s, p, ns, l2) : Bool}:
  match s:
    case T.Hidden{}:
      {==}
    case T.Shown{k}:
      %Equal.sym(Bool, B.mine(l1, p), B.mine(l2, p), agree_cell(w, h, l1, l2, ag, p, on)) :
        {Bool.and(Bool.not(_), Nat.is_eq(B.count_mines(l1, ns), k)) == Bool.and(Bool.not(B.mine(l2, p)), Nat.is_eq(B.count_mines(l2, ns), k)) : Bool}
      %Equal.sym(Nat, B.count_mines(l1, ns), B.count_mines(l2, ns), count_agree(w, h, l1, l2, ag, ns, ons)) :
        {Bool.and(Bool.not(B.mine(l2, p)), Nat.is_eq(_, k)) == Bool.and(Bool.not(B.mine(l2, p)), Nat.is_eq(B.count_mines(l2, ns), k)) : Bool}
      {==}
    case T.Boom{}:
      agree_cell(w, h, l1, l2, ag, p, on)

law items_ok_agree:
  for +w: Nat
  for +h: Nat
  for +l1: T.Grid(Bool)
  for +l2: T.Grid(Bool)
  for +ag: {agree(w, h, l1, l2) == True{} : Bool}
  for +its: List<&2, S.Item>
  for +ion: {items_onb(PS.WH{w, h}, its) == True{} : Bool}
  {S.items_ok(its, l1) == S.items_ok(its, l2) : Bool}

def items_ok_agree(w, h, l1, l2, ag, its, ion):
  match its:
    case Nil{}:
      {==}
    case S.Item{p, s, ns} <> t:
      +io = item_onb(PS.WH{w, h}, S.Item{p, s, ns})
      +io1 = P.and_true_l(io, items_onb(PS.WH{w, h}, t), ion)
      %Equal.sym(Bool, S.item_ok(s, p, ns, l1), S.item_ok(s, p, ns, l2),
        item_ok_agree(w, h, l1, l2, ag, p, s, ns,
          P.and_true_l(B.on_board(w, h, p), PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ns), io1),
          P.and_true_r(B.on_board(w, h, p), PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ns), io1))) :
        {Bool.and(_, S.items_ok(t, l1)) == Bool.and(S.item_ok(s, p, ns, l2), S.items_ok(t, l2)) : Bool}
      %Equal.sym(Bool, S.items_ok(t, l1), S.items_ok(t, l2),
        items_ok_agree(w, h, l1, l2, ag, t, P.and_true_r(io, items_onb(PS.WH{w, h}, t), ion))) :
        {Bool.and(S.item_ok(s, p, ns, l2), _) == Bool.and(S.item_ok(s, p, ns, l2), S.items_ok(t, l2)) : Bool}
      {==}

law check_agree:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +its: List<&2, S.Item>
  for +l1: T.Grid(Bool)
  for +l2: T.Grid(Bool)
  for +sh1: {B.shaped(Bool, w, h, l1) == True{} : Bool}
  for +sh2: {B.shaped(Bool, w, h, l2) == True{} : Bool}
  for +ag: {agree(w, h, l1, l2) == True{} : Bool}
  for +ion: {items_onb(PS.WH{w, h}, its) == True{} : Bool}
  {S.check(S.Ctx{w, h, n, rows, its}, l1) == S.check(S.Ctx{w, h, n, rows, its}, l2) : Bool}

def check_agree(w, h, n, rows, its, l1, l2, sh1, sh2, ag, ion):
  +sr = B.shaped(T.Seen, w, h, rows)
  %Equal.sym(Bool, B.shaped(Bool, w, h, l1), True{}, sh1) :
    {Bool.and(Bool.and(Bool.and(_, sr), Nat.is_eq(B.total_mines(l1), n)), S.items_ok(its, l1))
      == Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, l2), sr), Nat.is_eq(B.total_mines(l2), n)), S.items_ok(its, l2)) : Bool}
  %Equal.sym(Bool, B.shaped(Bool, w, h, l2), True{}, sh2) :
    {Bool.and(Bool.and(Bool.and(True{}, sr), Nat.is_eq(B.total_mines(l1), n)), S.items_ok(its, l1))
      == Bool.and(Bool.and(Bool.and(_, sr), Nat.is_eq(B.total_mines(l2), n)), S.items_ok(its, l2)) : Bool}
  %Equal.sym(Nat, B.total_mines(l1), B.total_mines(l2), total_agree(w, h, l1, l2, sh1, sh2, ag)) :
    {Bool.and(Bool.and(Bool.and(True{}, sr), Nat.is_eq(_, n)), S.items_ok(its, l1))
      == Bool.and(Bool.and(Bool.and(True{}, sr), Nat.is_eq(B.total_mines(l2), n)), S.items_ok(its, l2)) : Bool}
  %Equal.sym(Bool, S.items_ok(its, l1), S.items_ok(its, l2), items_ok_agree(w, h, l1, l2, ag, its, ion)) :
    {Bool.and(Bool.and(Bool.and(True{}, sr), Nat.is_eq(B.total_mines(l2), n)), _)
      == Bool.and(Bool.and(Bool.and(True{}, sr), Nat.is_eq(B.total_mines(l2), n)), S.items_ok(its, l2)) : Bool}
  {==}

# Coverage by the to-do list
# ==========================

def tcontains(ts: List<&2, S.Todo>, +q: T.Pos) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case S.Todo{c, rel} <> t:
      B.same(c, q) || tcontains(t, q)

type CV is Data:
  CV{todo: List<&2, S.Todo>, part: T.Grid(Maybe<&2, Bool>)}

def cv_f.go(e: CV, +q: T.Pos) -> Bool:
  match e:
    case CV{todo, part}:
      Bool.not(S.is_none(S.look(part, q))) || tcontains(todo, q)

def cv_f(e: CV, q: T.Pos) -> Bool:
  cv_f.go(e, q)

# Every unassigned cell of the board is still to do.
def covers(+w: Nat, +h: Nat, todo: List<&2, S.Todo>, part: T.Grid(Maybe<&2, Bool>)) -> Bool:
  PS.allp(~CV, ~cv_f, CV{todo, part}, B.cells(w, h))

def todos_ok(ts: List<&2, S.Todo>, +layout: T.Grid(Bool)) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case S.Todo{c, rel} <> t:
      S.items_ok(rel, layout) && todos_ok(t, layout)

def todos_onb(+e: PS.WH, ts: List<&2, S.Todo>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case S.Todo{c, rel} <> t:
      items_onb(e, rel) && todos_onb(e, t)

def covers_skip.cell(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +q: T.Pos, fr: {S.is_none(S.look(part, c)) == False{} : Bool},
  h: {cv_f(CV{S.Todo{c, rel} <> rest, part}, q) == True{} : Bool}, +b: Bool, be: {B.same(c, q) == b : Bool}) ->
  {cv_f(CV{rest, part}, q) == True{} : Bool}:
  match b:
    case True{}:
      %PG.same_sound(c, q, be) :
        {Bool.or(Bool.not(S.is_none(S.look(part, _))), tcontains(rest, _)) == True{} : Bool}
      %Equal.sym(Bool, S.is_none(S.look(part, c)), False{}, fr) :
        {Bool.or(Bool.not(_), tcontains(rest, c)) == True{} : Bool}
      {==}
    case False{}:
      %be : {Bool.or(Bool.not(S.is_none(S.look(part, q))), Bool.or(_, tcontains(rest, q))) == True{} : Bool}; h

law covers_skip:
  for +c: T.Pos
  for +rel: List<&2, S.Item>
  for +rest: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +fr: {S.is_none(S.look(part, c)) == False{} : Bool}
  for +ps: List<&2, T.Pos>
  for +cv: {PS.allp(~CV, ~cv_f, CV{S.Todo{c, rel} <> rest, part}, ps) == True{} : Bool}
  {PS.allp(~CV, ~cv_f, CV{rest, part}, ps) == True{} : Bool}

def covers_skip(c, rel, rest, part, fr, ps, cv):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +e0 = {CV{S.Todo{c, rel} <> rest, part} : CV}
      %Equal.sym(Bool, cv_f(CV{rest, part}, q), True{},
        covers_skip.cell(c, rel, rest, part, q, fr, PS.allp_head(~CV, ~cv_f, e0, q, t, cv), B.same(c, q), {==})) :
        {Bool.and(_, PS.allp(~CV, ~cv_f, CV{rest, part}, t)) == True{} : Bool}
      covers_skip(c, rel, rest, part, fr, t, PS.allp_tail(~CV, ~cv_f, e0, q, t, cv))

def set_look(+w: Nat, +h: Nat, +part: T.Grid(Maybe<&2, Bool>), +q: T.Pos, +v: Maybe<&2, Bool>,
  sh: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, on: {B.on_board(w, h, q) == True{} : Bool}) ->
  {S.look(B.set_at(Maybe<&2, Bool>, part, q, v), q) == v : Maybe<&2, Bool>}:
  match q:
    case T.Pos{x, y}:
      PL.at_set_eq(Maybe<&2, Bool>, w, h, part, x, y, v, None{}, sh, on)

def covers_set.cell(+w: Nat, +h: Nat, +c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>,
  +part: T.Grid(Maybe<&2, Bool>), +bv: Bool, +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool},
  +q: T.Pos, on: {B.on_board(w, h, q) == True{} : Bool},
  h0: {cv_f(CV{S.Todo{c, rel} <> rest, part}, q) == True{} : Bool}, +b: Bool, +be: {B.same(c, q) == b : Bool}) ->
  {cv_f(CV{rest, B.set_at(Maybe<&2, Bool>, part, c, Some{bv})}, q) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(T.Pos, c, q, PG.same_sound(c, q, be)) :
        {Bool.or(Bool.not(S.is_none(S.look(B.set_at(Maybe<&2, Bool>, part, _, Some{bv}), q))), tcontains(rest, q)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Bool>, S.look(B.set_at(Maybe<&2, Bool>, part, q, Some{bv}), q), Some{bv},
        set_look(w, h, part, q, Some{bv}, shP, on)) :
        {Bool.or(Bool.not(S.is_none(_)), tcontains(rest, q)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Bool>, S.look(B.set_at(Maybe<&2, Bool>, part, c, Some{bv}), q), S.look(part, q),
        PL.at_set_ne(Maybe<&2, Bool>, part, c, q, Some{bv}, None{}, be)) :
        {Bool.or(Bool.not(S.is_none(_)), tcontains(rest, q)) == True{} : Bool}
      %be : {Bool.or(Bool.not(S.is_none(S.look(part, q))), Bool.or(_, tcontains(rest, q))) == True{} : Bool}; h0

law covers_set:
  for +w: Nat
  for +h: Nat
  for +c: T.Pos
  for +rel: List<&2, S.Item>
  for +rest: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +bv: Bool
  for +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  for +cv: {PS.allp(~CV, ~cv_f, CV{S.Todo{c, rel} <> rest, part}, ps) == True{} : Bool}
  {PS.allp(~CV, ~cv_f, CV{rest, B.set_at(Maybe<&2, Bool>, part, c, Some{bv})}, ps) == True{} : Bool}

def covers_set(w, h, c, rel, rest, part, bv, shP, ps, ons, cv):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +e0 = {CV{S.Todo{c, rel} <> rest, part} : CV}
      +e1 = {CV{rest, B.set_at(Maybe<&2, Bool>, part, c, Some{bv})} : CV}
      %Equal.sym(Bool, cv_f(e1, q), True{},
        covers_set.cell(w, h, c, rel, rest, part, bv, shP, q, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons),
          PS.allp_head(~CV, ~cv_f, e0, q, t, cv), B.same(c, q), {==})) :
        {Bool.and(_, PS.allp(~CV, ~cv_f, e1, t)) == True{} : Bool}
      covers_set(w, h, c, rel, rest, part, bv, shP, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons),
        PS.allp_tail(~CV, ~cv_f, e0, q, t, cv))

def comp_set.cell(+w: Nat, +h: Nat, +c: T.Pos, +part: T.Grid(Maybe<&2, Bool>), +layout: T.Grid(Bool), +bv: Bool,
  +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, mc: {B.mine(layout, c) == bv : Bool},
  +q: T.Pos, on: {B.on_board(w, h, q) == True{} : Bool},
  h0: {cmp_f(CE{part, layout}, q) == True{} : Bool}, +b: Bool, +be: {B.same(c, q) == b : Bool}) ->
  {cmp_f(CE{B.set_at(Maybe<&2, Bool>, part, c, Some{bv}), layout}, q) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(T.Pos, c, q, PG.same_sound(c, q, be)) :
        {cmp_cell(S.look(B.set_at(Maybe<&2, Bool>, part, _, Some{bv}), q), B.mine(layout, q)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Bool>, S.look(B.set_at(Maybe<&2, Bool>, part, q, Some{bv}), q), Some{bv},
        set_look(w, h, part, q, Some{bv}, shP, on)) :
        {cmp_cell(_, B.mine(layout, q)) == True{} : Bool}
      %PG.same_sound(c, q, be) : {beq(B.mine(layout, _), bv) == True{} : Bool}
      %Equal.sym(Bool, B.mine(layout, c), bv, mc) : {beq(_, bv) == True{} : Bool}
      beq_refl(bv)
    case False{}:
      %Equal.sym(Maybe<&2, Bool>, S.look(B.set_at(Maybe<&2, Bool>, part, c, Some{bv}), q), S.look(part, q),
        PL.at_set_ne(Maybe<&2, Bool>, part, c, q, Some{bv}, None{}, be)) :
        {cmp_cell(_, B.mine(layout, q)) == True{} : Bool}
      h0

law comp_set:
  for +w: Nat
  for +h: Nat
  for +c: T.Pos
  for +part: T.Grid(Maybe<&2, Bool>)
  for +layout: T.Grid(Bool)
  for +bv: Bool
  for +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +mc: {B.mine(layout, c) == bv : Bool}
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  for +cm: {PS.allp(~CE, ~cmp_f, CE{part, layout}, ps) == True{} : Bool}
  {PS.allp(~CE, ~cmp_f, CE{B.set_at(Maybe<&2, Bool>, part, c, Some{bv}), layout}, ps) == True{} : Bool}

def comp_set(w, h, c, part, layout, bv, shP, mc, ps, ons, cm):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +e0 = {CE{part, layout} : CE}
      +e1 = {CE{B.set_at(Maybe<&2, Bool>, part, c, Some{bv}), layout} : CE}
      %Equal.sym(Bool, cmp_f(e1, q), True{},
        comp_set.cell(w, h, c, part, layout, bv, shP, mc, q, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons),
          PS.allp_head(~CE, ~cmp_f, e0, q, t, cm), B.same(c, q), {==})) :
        {Bool.and(_, PS.allp(~CE, ~cmp_f, e1, t)) == True{} : Bool}
      comp_set(w, h, c, part, layout, bv, shP, mc, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons),
        PS.allp_tail(~CE, ~cmp_f, e0, q, t, cm))

# The search is complete
# ======================

def leaf_cell.go(+part: T.Grid(Maybe<&2, Bool>), +layout: T.Grid(Bool), +q: T.Pos, +m: Maybe<&2, Bool>,
  me: {S.look(part, q) == m : Maybe<&2, Bool>},
  cv: {Bool.not(S.is_none(m)) == True{} : Bool}, cm: {cmp_cell(m, B.mine(layout, q)) == True{} : Bool}) ->
  {beq(B.mine(S.fill(part), q), B.mine(layout, q)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({beq(B.mine(S.fill(part), q), B.mine(layout, q)) == True{} : Bool}, P.false_ne_true(cv))
    case Some{c}:
      %Equal.sym(Bool, B.mine(S.fill(part), q), Maybe.default(&2, Bool, S.look(part, q), False{}), fill_at(part, q)) :
        {beq(_, B.mine(layout, q)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Bool>, S.look(part, q), Some{c}, me) : {beq(Maybe.default(&2, Bool, _, False{}), B.mine(layout, q)) == True{} : Bool}
      %Equal.sym(Bool, B.mine(layout, q), c, beq_sound(B.mine(layout, q), c, cm)) : {beq(c, _) == True{} : Bool}
      beq_refl(c)

law leaf_agree:
  for +part: T.Grid(Maybe<&2, Bool>)
  for +layout: T.Grid(Bool)
  for +ps: List<&2, T.Pos>
  for +cv: {PS.allp(~CV, ~cv_f, CV{Nil{}, part}, ps) == True{} : Bool}
  for +cm: {PS.allp(~CE, ~cmp_f, CE{part, layout}, ps) == True{} : Bool}
  {PS.allp(~AG, ~ag_f, AG{S.fill(part), layout}, ps) == True{} : Bool}

def leaf_agree(part, layout, ps, cv, cm):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +e0 = {CV{Nil{}, part} : CV}
      +e1 = {CE{part, layout} : CE}
      +cvq = {%P.or_false_r(Bool.not(S.is_none(S.look(part, q)))) : {_ == True{} : Bool};
        PS.allp_head(~CV, ~cv_f, e0, q, t, cv) : {Bool.not(S.is_none(S.look(part, q))) == True{} : Bool}}
      %Equal.sym(Bool, ag_f(AG{S.fill(part), layout}, q), True{},
        leaf_cell.go(part, layout, q, S.look(part, q), {==}, cvq, PS.allp_head(~CE, ~cmp_f, e1, q, t, cm))) :
        {Bool.and(_, PS.allp(~AG, ~ag_f, AG{S.fill(part), layout}, t)) == True{} : Bool}
      leaf_agree(part, layout, t, PS.allp_tail(~CV, ~cv_f, e0, q, t, cv), PS.allp_tail(~CE, ~cmp_f, e1, q, t, cm))

def disc_some(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{v}:
      Unit

def some_ne_none(-A: Data, -a: A, e: {Some{a} == None{} : Maybe<&2, A>}) -> Empty:
  %e : disc_some(A, _)
  Unit{}

def dfs_when_none(ok: Bool, k: Unit -> Maybe<&2, T.Grid(Bool)>, e: {S.dfs.when(ok, k) == None{} : Maybe<&2, T.Grid(Bool)>},
  okt: {ok == True{} : Bool}) -> {k(Unit{}) == None{} : Maybe<&2, T.Grid(Bool)>}:
  match ok:
    case True{}:
      e
    case False{}:
      Empty.absurd({k(Unit{}) == None{} : Maybe<&2, T.Grid(Bool)>}, P.false_ne_true(okt))

def dfs_or_none_l(r: Maybe<&2, T.Grid(Bool)>, k: Unit -> Maybe<&2, T.Grid(Bool)>,
  e: {S.dfs.or(r, k) == None{} : Maybe<&2, T.Grid(Bool)>}) -> {r == None{} : Maybe<&2, T.Grid(Bool)>}:
  match r:
    case None{}:
      {==}
    case Some{l}:
      Empty.absurd({Some{l} == None{} : Maybe<&2, T.Grid(Bool)>}, some_ne_none(T.Grid(Bool), l, e))

def dfs_or_none_r(r: Maybe<&2, T.Grid(Bool)>, k: Unit -> Maybe<&2, T.Grid(Bool)>,
  e: {S.dfs.or(r, k) == None{} : Maybe<&2, T.Grid(Bool)>}) -> {k(Unit{}) == None{} : Maybe<&2, T.Grid(Bool)>}:
  match r:
    case None{}:
      e
    case Some{l}:
      Empty.absurd({k(Unit{}) == None{} : Maybe<&2, T.Grid(Bool)>}, some_ne_none(T.Grid(Bool), l, e))

def dfs_none.pick(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +its: List<&2, S.Item>, +layout: T.Grid(Bool),
  +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, +shL: {B.shaped(Bool, w, h, layout) == True{} : Bool},
  +cov: {covers(w, h, S.Todo{c, rel} <> rest, part) == True{} : Bool},
  +comp: {completes(w, h, part, layout) == True{} : Bool}, +tot: {B.total_mines(layout) == n : Nat},
  +rok: {S.items_ok(rel, layout) == True{} : Bool}, +ron: {items_onb(PS.WH{w, h}, rel) == True{} : Bool},
  +bl: Bool, ble: {B.mine(layout, c) == bl : Bool},
  e: {S.dfs.or(S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel, n),
       x => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), S.Ctx{w, h, n, rows, its})),
     y => S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel, n),
       z => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), S.Ctx{w, h, n, rows, its}))) == None{} : Maybe<&2, T.Grid(Bool)>},
  k0: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Grid(Bool)>} ->
    {covers(w, h, rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}})) == True{} : Bool} ->
    {completes(w, h, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), layout) == True{} : Bool} -> Empty,
  k1: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Grid(Bool)>} ->
    {covers(w, h, rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}})) == True{} : Bool} ->
    {completes(w, h, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), layout) == True{} : Bool} -> Empty) -> Empty:
  match bl:
    case False{}:
      +p0 = B.set_at(Maybe<&2, Bool>, part, c, Some{False{}})
      +comp0 = comp_set(w, h, c, part, layout, False{}, shP, ble, B.cells(w, h), PS.cells_on(w, h), comp)
      +ok0 = open_ok_sound(w, h, n, p0, rel, layout, PL.shaped_set(Maybe<&2, Bool>, w, h, part, c, Some{False{}}, shP),
        shL, comp0, tot, rok, ron)
      +ctx = {S.Ctx{w, h, n, rows, its} : S.Ctx}
      k0(dfs_when_none(S.open_ok(p0, rel, n), x => S.dfs(rest, p0, ctx),
          dfs_or_none_l(S.dfs.when(S.open_ok(p0, rel, n), x => S.dfs(rest, p0, ctx)),
            y => S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel, n),
              z => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx)), e), ok0),
        covers_set(w, h, c, rel, rest, part, False{}, shP, B.cells(w, h), PS.cells_on(w, h), cov), comp0)
    case True{}:
      +p1 = B.set_at(Maybe<&2, Bool>, part, c, Some{True{}})
      +comp1 = comp_set(w, h, c, part, layout, True{}, shP, ble, B.cells(w, h), PS.cells_on(w, h), comp)
      +ok1 = open_ok_sound(w, h, n, p1, rel, layout, PL.shaped_set(Maybe<&2, Bool>, w, h, part, c, Some{True{}}, shP),
        shL, comp1, tot, rok, ron)
      +ctx = {S.Ctx{w, h, n, rows, its} : S.Ctx}
      k1(dfs_when_none(S.open_ok(p1, rel, n), z => S.dfs(rest, p1, ctx),
          dfs_or_none_r(S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel, n),
              x => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx)),
            y => S.dfs.when(S.open_ok(p1, rel, n), z => S.dfs(rest, p1, ctx)), e), ok1),
        covers_set(w, h, c, rel, rest, part, True{}, shP, B.cells(w, h), PS.cells_on(w, h), cov), comp1)

def dfs_none.node(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +its: List<&2, S.Item>, +layout: T.Grid(Bool),
  +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, +shL: {B.shaped(Bool, w, h, layout) == True{} : Bool},
  +cov: {covers(w, h, S.Todo{c, rel} <> rest, part) == True{} : Bool},
  +comp: {completes(w, h, part, layout) == True{} : Bool}, +tot: {B.total_mines(layout) == n : Nat},
  +rok: {S.items_ok(rel, layout) == True{} : Bool}, +ron: {items_onb(PS.WH{w, h}, rel) == True{} : Bool},
  +fr: Bool, fre: {S.is_none(S.look(part, c)) == fr : Bool},
  e: {S.dfs.free(fr, u => S.dfs(rest, part, S.Ctx{w, h, n, rows, its}),
      v => S.dfs.or(S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel, n),
        x => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), S.Ctx{w, h, n, rows, its})),
      y => S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel, n),
        z => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), S.Ctx{w, h, n, rows, its})))) == None{} : Maybe<&2, T.Grid(Bool)>},
  kp: {S.dfs(rest, part, S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Grid(Bool)>} ->
    {covers(w, h, rest, part) == True{} : Bool} -> Empty,
  k0: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Grid(Bool)>} ->
    {covers(w, h, rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}})) == True{} : Bool} ->
    {completes(w, h, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), layout) == True{} : Bool} -> Empty,
  k1: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Grid(Bool)>} ->
    {covers(w, h, rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}})) == True{} : Bool} ->
    {completes(w, h, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), layout) == True{} : Bool} -> Empty) -> Empty:
  match fr:
    case False{}:
      kp(e, covers_skip(c, rel, rest, part, fre, B.cells(w, h), cov))
    case True{}:
      dfs_none.pick(c, rel, rest, part, w, h, n, rows, its, layout, shP, shL, cov, comp, tot, rok, ron,
        B.mine(layout, c), {==}, e, k0, k1)

law chk_total:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +its: List<&2, S.Item>
  for +layout: T.Grid(Bool)
  for chk: {S.check(S.Ctx{w, h, n, rows, its}, layout) == True{} : Bool}
  {B.total_mines(layout) == n : Nat}

def chk_total(w, h, n, rows, its, layout, chk):
  +a = Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows))
  +b = Nat.is_eq(B.total_mines(layout), n)
  P.eq_sound(B.total_mines(layout), n,
    P.and_true_r(a, b, P.and_true_l(Bool.and(a, b), S.items_ok(its, layout), chk)))

# If the search finds nothing, no consistent layout completes the partial
# layout (given that every unassigned cell is still to do).
law dfs_none:
  for +todo: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +its: List<&2, S.Item>
  for +layout: T.Grid(Bool)
  for e: {S.dfs(todo, part, S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Grid(Bool)>}
  for +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +shL: {B.shaped(Bool, w, h, layout) == True{} : Bool}
  for +cov: {covers(w, h, todo, part) == True{} : Bool}
  for +comp: {completes(w, h, part, layout) == True{} : Bool}
  for +chk: {S.check(S.Ctx{w, h, n, rows, its}, layout) == True{} : Bool}
  for +tok: {todos_ok(todo, layout) == True{} : Bool}
  for +ton: {todos_onb(PS.WH{w, h}, todo) == True{} : Bool}
  for +ion: {items_onb(PS.WH{w, h}, its) == True{} : Bool}
  Empty

def dfs_none(todo, part, w, h, n, rows, its, layout, e, shP, shL, cov, comp, chk, tok, ton, ion):
  match todo:
    case Nil{}:
      +fp = S.fill(part)
      +shF = Equal.trans(Bool, B.shaped(Bool, w, h, fp), B.shaped(Maybe<&2, Bool>, w, h, part), True{},
        fill_shaped(w, h, part), shP)
      +agF = leaf_agree(part, layout, B.cells(w, h), cov, comp)
      +cf = Equal.trans(Bool, S.check(S.Ctx{w, h, n, rows, its}, fp), S.check(S.Ctx{w, h, n, rows, its}, layout), True{},
        check_agree(w, h, n, rows, its, fp, layout, shF, shL, agF, ion), chk)
      some_ne_none(T.Grid(Bool), fp,
        {%cf : {Bool.pick(Maybe<&2, T.Grid(Bool)>, _, Some{fp}, None{}) == None{} : Maybe<&2, T.Grid(Bool)>};
          e : {Some{fp} == None{} : Maybe<&2, T.Grid(Bool)>}})
    case S.Todo{c, rel} <> rest:
      +rok = P.and_true_l(S.items_ok(rel, layout), todos_ok(rest, layout), tok)
      +tokr = P.and_true_r(S.items_ok(rel, layout), todos_ok(rest, layout), tok)
      +ron = P.and_true_l(items_onb(PS.WH{w, h}, rel), todos_onb(PS.WH{w, h}, rest), ton)
      +tonr = P.and_true_r(items_onb(PS.WH{w, h}, rel), todos_onb(PS.WH{w, h}, rest), ton)
      +tot = chk_total(w, h, n, rows, its, layout, chk)
      dfs_none.node(c, rel, rest, part, w, h, n, rows, its, layout, shP, shL, cov, comp, tot, rok, ron,
        S.is_none(S.look(part, c)), {==}, e,
        e2 => cv2 => dfs_none(rest, part, w, h, n, rows, its, layout, e2, shP, shL, cv2, comp, chk, tokr, tonr, ion),
        e2 => cv2 => cm2 => dfs_none(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), w, h, n, rows, its, layout, e2,
          PL.shaped_set(Maybe<&2, Bool>, w, h, part, c, Some{False{}}, shP), shL, cv2, cm2, chk, tokr, tonr, ion),
        e2 => cv2 => cm2 => dfs_none(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), w, h, n, rows, its, layout, e2,
          PL.shaped_set(Maybe<&2, Bool>, w, h, part, c, Some{True{}}, shP), shL, cv2, cm2, chk, tokr, tonr, ion))

# What the search finds is a real candidate
# =========================================

def dfs_when_some(ok: Bool, k: Unit -> Maybe<&2, T.Grid(Bool)>, -l: T.Grid(Bool),
  e: {S.dfs.when(ok, k) == Some{l} : Maybe<&2, T.Grid(Bool)>}) -> {k(Unit{}) == Some{l} : Maybe<&2, T.Grid(Bool)>}:
  match ok:
    case True{}:
      e
    case False{}:
      Empty.absurd({k(Unit{}) == Some{l} : Maybe<&2, T.Grid(Bool)>}, PL.none_ne_some(T.Grid(Bool), l, e))

def dfs_or_some(r: Maybe<&2, T.Grid(Bool)>, k: Unit -> Maybe<&2, T.Grid(Bool)>, -l: T.Grid(Bool),
  e: {S.dfs.or(r, k) == Some{l} : Maybe<&2, T.Grid(Bool)>}) ->
  Or({r == Some{l} : Maybe<&2, T.Grid(Bool)>}, {k(Unit{}) == Some{l} : Maybe<&2, T.Grid(Bool)>}):
  match r:
    case None{}:
      Inr{e}
    case Some{x}:
      Inl{e}

def BranchSome(+d0: Maybe<&2, T.Grid(Bool)>, +d1: Maybe<&2, T.Grid(Bool)>, +l: T.Grid(Bool)) -> Type:
  Or({d0 == Some{l} : Maybe<&2, T.Grid(Bool)>}, {d1 == Some{l} : Maybe<&2, T.Grid(Bool)>})

def dfs_branch_some.k(+ok0: Bool, +ok1: Bool, +d0: Maybe<&2, T.Grid(Bool)>, +d1: Maybe<&2, T.Grid(Bool)>, +l: T.Grid(Bool),
  r: Or({S.dfs.when(ok0, x => d0) == Some{l} : Maybe<&2, T.Grid(Bool)>},
    {S.dfs.when(ok1, z => d1) == Some{l} : Maybe<&2, T.Grid(Bool)>})) -> BranchSome(d0, d1, l):
  match r:
    case Inl{e0}:
      Inl{dfs_when_some(ok0, x => d0, l, e0)}
    case Inr{e1}:
      Inr{dfs_when_some(ok1, z => d1, l, e1)}

def dfs_branch_some(+ok0: Bool, +ok1: Bool, +d0: Maybe<&2, T.Grid(Bool)>, +d1: Maybe<&2, T.Grid(Bool)>, +l: T.Grid(Bool),
  e: {S.dfs.or(S.dfs.when(ok0, x => d0), y => S.dfs.when(ok1, z => d1)) == Some{l} : Maybe<&2, T.Grid(Bool)>}) ->
  BranchSome(d0, d1, l):
  dfs_branch_some.k(ok0, ok1, d0, d1, l,
    dfs_or_some(S.dfs.when(ok0, x => d0), y => S.dfs.when(ok1, z => d1), l, e))

def leaf_some(+ctx: S.Ctx, +f: T.Grid(Bool), +l: T.Grid(Bool), +b: Bool, be: {S.check(ctx, f) == b : Bool},
  e: {Bool.pick(Maybe<&2, T.Grid(Bool)>, b, Some{f}, None{}) == Some{l} : Maybe<&2, T.Grid(Bool)>}) ->
  {f == l : T.Grid(Bool)} & {S.check(ctx, f) == True{} : Bool}:
  match b:
    case True{}:
      (PL.some_inj(T.Grid(Bool), f, l, e), be)
    case False{}:
      Empty.absurd({f == l : T.Grid(Bool)} & {S.check(ctx, f) == True{} : Bool}, PL.none_ne_some(T.Grid(Bool), l, e))

def leaf_check.k(+ctx: S.Ctx, +f: T.Grid(Bool), +l: T.Grid(Bool),
  r: {f == l : T.Grid(Bool)} & {S.check(ctx, f) == True{} : Bool}) -> {S.check(ctx, l) == True{} : Bool}:
  match r:
    case (fl, ck):
      %fl : {S.check(ctx, _) == True{} : Bool}
      ck

# A layout the search returns passes the consistency check.
law dfs_some_check:
  for +todo: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +ctx: S.Ctx
  for +l: T.Grid(Bool)
  for e: {S.dfs(todo, part, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>}
  {S.check(ctx, l) == True{} : Bool}

def dfs_some_check.br(+l: T.Grid(Bool), +ctx: S.Ctx, +d0: Maybe<&2, T.Grid(Bool)>, +d1: Maybe<&2, T.Grid(Bool)>,
  r: BranchSome(d0, d1, l), k0: {d0 == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {S.check(ctx, l) == True{} : Bool},
  k1: {d1 == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {S.check(ctx, l) == True{} : Bool}) -> {S.check(ctx, l) == True{} : Bool}:
  match r:
    case Inl{e0}:
      k0(e0)
    case Inr{e1}:
      k1(e1)

def dfs_some_check.node(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +ctx: S.Ctx, +l: T.Grid(Bool), +fr: Bool,
  e: {S.dfs.free(fr, u => S.dfs(rest, part, ctx),
      v => S.dfs.or(S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel, S.ctx_n(ctx)),
        x => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx)),
      y => S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel, S.ctx_n(ctx)),
        z => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx)))) == Some{l} : Maybe<&2, T.Grid(Bool)>},
  kp: {S.dfs(rest, part, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {S.check(ctx, l) == True{} : Bool},
  k0: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.check(ctx, l) == True{} : Bool},
  k1: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.check(ctx, l) == True{} : Bool}) -> {S.check(ctx, l) == True{} : Bool}:
  match fr:
    case False{}:
      kp(e)
    case True{}:
      dfs_some_check.br(l, ctx, S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx),
        S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx),
        dfs_branch_some(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel, S.ctx_n(ctx)),
          S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel, S.ctx_n(ctx)),
          S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx),
          S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx), l, e), k0, k1)

def dfs_some_check(todo, part, ctx, l, e):
  match todo:
    case Nil{}:
      leaf_check.k(ctx, S.fill(part), l, leaf_some(ctx, S.fill(part), l, S.check(ctx, S.fill(part)), {==}, e))
    case S.Todo{c, rel} <> rest:
      dfs_some_check.node(c, rel, rest, part, ctx, l, S.is_none(S.look(part, c)), e,
        e2 => dfs_some_check(rest, part, ctx, l, e2),
        e2 => dfs_some_check(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx, l, e2),
        e2 => dfs_some_check(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx, l, e2))

def set_keep(+part: T.Grid(Maybe<&2, Bool>), +c: T.Pos, +q: T.Pos, +v: Maybe<&2, Bool>, +bq: Bool,
  fre: {S.is_none(S.look(part, c)) == True{} : Bool}, lq: {S.look(part, q) == Some{bq} : Maybe<&2, Bool>},
  +b: Bool, be: {B.same(c, q) == b : Bool}) ->
  {S.look(B.set_at(Maybe<&2, Bool>, part, c, v), q) == Some{bq} : Maybe<&2, Bool>}:
  match b:
    case True{}:
      +lc = {%Equal.sym(T.Pos, c, q, PG.same_sound(c, q, be)) : {S.look(part, _) == Some{bq} : Maybe<&2, Bool>};
        lq : {S.look(part, c) == Some{bq} : Maybe<&2, Bool>}}
      Empty.absurd({S.look(B.set_at(Maybe<&2, Bool>, part, c, v), q) == Some{bq} : Maybe<&2, Bool>},
        P.false_ne_true(%lc : {S.is_none(_) == True{} : Bool}; fre))
    case False{}:
      %Equal.sym(Maybe<&2, Bool>, S.look(B.set_at(Maybe<&2, Bool>, part, c, v), q), S.look(part, q),
        PL.at_set_ne(Maybe<&2, Bool>, part, c, q, v, None{}, be)) : {_ == Some{bq} : Maybe<&2, Bool>}
      lq

def leaf_keep(+ctx: S.Ctx, +part: T.Grid(Maybe<&2, Bool>), +l: T.Grid(Bool), +q: T.Pos, +bq: Bool,
  lq: {S.look(part, q) == Some{bq} : Maybe<&2, Bool>},
  r: {S.fill(part) == l : T.Grid(Bool)} & {S.check(ctx, S.fill(part)) == True{} : Bool}) ->
  {B.mine(l, q) == bq : Bool}:
  match r:
    case (fl, ck):
      %fl : {B.mine(_, q) == bq : Bool}
      %Equal.sym(Bool, B.mine(S.fill(part), q), Maybe.default(&2, Bool, S.look(part, q), False{}), fill_at(part, q)) :
        {_ == bq : Bool}
      %Equal.sym(Maybe<&2, Bool>, S.look(part, q), Some{bq}, lq) : {Maybe.default(&2, Bool, _, False{}) == bq : Bool}
      {==}

def dfs_some_keep.br(+l: T.Grid(Bool), +q: T.Pos, +bq: Bool, +d0: Maybe<&2, T.Grid(Bool)>, +d1: Maybe<&2, T.Grid(Bool)>,
  r: BranchSome(d0, d1, l), k0: {d0 == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {B.mine(l, q) == bq : Bool},
  k1: {d1 == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {B.mine(l, q) == bq : Bool}) -> {B.mine(l, q) == bq : Bool}:
  match r:
    case Inl{e0}:
      k0(e0)
    case Inr{e1}:
      k1(e1)

def dfs_some_keep.node(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +ctx: S.Ctx, +l: T.Grid(Bool), +q: T.Pos, +bq: Bool, +fr: Bool, +fre: {S.is_none(S.look(part, c)) == fr : Bool},
  e: {S.dfs.free(fr, u => S.dfs(rest, part, ctx),
      v => S.dfs.or(S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel, S.ctx_n(ctx)),
        x => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx)),
      y => S.dfs.when(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel, S.ctx_n(ctx)),
        z => S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx)))) == Some{l} : Maybe<&2, T.Grid(Bool)>},
  +lq: {S.look(part, q) == Some{bq} : Maybe<&2, Bool>},
  kp: {S.dfs(rest, part, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {B.mine(l, q) == bq : Bool},
  k0: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.look(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), q) == Some{bq} : Maybe<&2, Bool>} -> {B.mine(l, q) == bq : Bool},
  k1: {S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.look(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), q) == Some{bq} : Maybe<&2, Bool>} -> {B.mine(l, q) == bq : Bool}) ->
  {B.mine(l, q) == bq : Bool}:
  match fr:
    case False{}:
      kp(e)
    case True{}:
      +d0 = S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx)
      +d1 = S.dfs(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx)
      dfs_some_keep.br(l, q, bq, d0, d1,
        dfs_branch_some(S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel, S.ctx_n(ctx)),
          S.open_ok(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel, S.ctx_n(ctx)), d0, d1, l, e),
        e0 => k0(e0, set_keep(part, c, q, Some{False{}}, bq, fre, lq, B.same(c, q), {==})),
        e1 => k1(e1, set_keep(part, c, q, Some{True{}}, bq, fre, lq, B.same(c, q), {==})))

# A layout the search returns keeps every cell the partial layout fixed.
law dfs_some_keep:
  for +todo: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +ctx: S.Ctx
  for +l: T.Grid(Bool)
  for e: {S.dfs(todo, part, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>}
  for +q: T.Pos
  for +bq: Bool
  for +lq: {S.look(part, q) == Some{bq} : Maybe<&2, Bool>}
  {B.mine(l, q) == bq : Bool}

def dfs_some_keep(todo, part, ctx, l, e, q, bq, lq):
  match todo:
    case Nil{}:
      leaf_keep(ctx, part, l, q, bq, lq, leaf_some(ctx, S.fill(part), l, S.check(ctx, S.fill(part)), {==}, e))
    case S.Todo{c, rel} <> rest:
      dfs_some_keep.node(c, rel, rest, part, ctx, l, q, bq, S.is_none(S.look(part, c)), {==}, e, lq,
        e2 => dfs_some_keep(rest, part, ctx, l, e2, q, bq, lq),
        e2 => l2 => dfs_some_keep(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), ctx, l, e2, q, bq, l2),
        e2 => l2 => dfs_some_keep(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx, l, e2, q, bq, l2))

# The same for the counting search
# =================================

# A layout the counting search returns passes the consistency check.
law dfs2_some_check:
  for +todo: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +t: Nat
  for +f: Nat
  for +ctx: S.Ctx
  for +l: T.Grid(Bool)
  for e: {S.dfs2(todo, part, t, f, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>}
  {S.check(ctx, l) == True{} : Bool}

def dfs2_some_check.node(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +t: Nat, +f: Nat, +ctx: S.Ctx, +l: T.Grid(Bool), +fr: Bool,
  e: {S.dfs.free(fr, u => S.dfs2(rest, part, t, f, ctx),
      v => S.dfs.or(S.dfs.when(Bool.and(S.between(t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel)),
        x => S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx)),
      y => S.dfs.when(Bool.and(S.between(1n+t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel)),
        z => S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx)))) == Some{l} : Maybe<&2, T.Grid(Bool)>},
  kp: {S.dfs2(rest, part, t, f, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {S.check(ctx, l) == True{} : Bool},
  k0: {S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.check(ctx, l) == True{} : Bool},
  k1: {S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.check(ctx, l) == True{} : Bool}) -> {S.check(ctx, l) == True{} : Bool}:
  match fr:
    case False{}:
      kp(e)
    case True{}:
      dfs_some_check.br(l, ctx, S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx),
        S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx),
        dfs_branch_some(Bool.and(S.between(t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel)),
          Bool.and(S.between(1n+t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel)),
          S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx),
          S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx), l, e), k0, k1)

def dfs2_some_check(todo, part, t, f, ctx, l, e):
  match todo:
    case Nil{}:
      leaf_check.k(ctx, S.fill(part), l, leaf_some(ctx, S.fill(part), l, S.check(ctx, S.fill(part)), {==}, e))
    case S.Todo{c, rel} <> rest:
      dfs2_some_check.node(c, rel, rest, part, t, f, ctx, l, S.is_none(S.look(part, c)), e,
        e2 => dfs2_some_check(rest, part, t, f, ctx, l, e2),
        e2 => dfs2_some_check(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx, l, e2),
        e2 => dfs2_some_check(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx, l, e2))

# A layout the counting search returns keeps every cell the partial layout fixed.
law dfs2_some_keep:
  for +todo: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +t: Nat
  for +f: Nat
  for +ctx: S.Ctx
  for +l: T.Grid(Bool)
  for e: {S.dfs2(todo, part, t, f, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>}
  for +q: T.Pos
  for +bq: Bool
  for +lq: {S.look(part, q) == Some{bq} : Maybe<&2, Bool>}
  {B.mine(l, q) == bq : Bool}

def dfs2_some_keep.node(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +part: T.Grid(Maybe<&2, Bool>),
  +t: Nat, +f: Nat, +ctx: S.Ctx, +l: T.Grid(Bool), +q: T.Pos, +bq: Bool, +fr: Bool, +fre: {S.is_none(S.look(part, c)) == fr : Bool},
  e: {S.dfs.free(fr, u => S.dfs2(rest, part, t, f, ctx),
      v => S.dfs.or(S.dfs.when(Bool.and(S.between(t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel)),
        x => S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx)),
      y => S.dfs.when(Bool.and(S.between(1n+t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel)),
        z => S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx)))) == Some{l} : Maybe<&2, T.Grid(Bool)>},
  +lq: {S.look(part, q) == Some{bq} : Maybe<&2, Bool>},
  kp: {S.dfs2(rest, part, t, f, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} -> {B.mine(l, q) == bq : Bool},
  k0: {S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.look(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), q) == Some{bq} : Maybe<&2, Bool>} -> {B.mine(l, q) == bq : Bool},
  k1: {S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} ->
    {S.look(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), q) == Some{bq} : Maybe<&2, Bool>} -> {B.mine(l, q) == bq : Bool}) ->
  {B.mine(l, q) == bq : Bool}:
  match fr:
    case False{}:
      kp(e)
    case True{}:
      +d0 = S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx)
      +d1 = S.dfs2(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx)
      dfs_some_keep.br(l, q, bq, d0, d1,
        dfs_branch_some(Bool.and(S.between(t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), rel)),
          Bool.and(S.between(1n+t, Nat.sub(f, 1n), S.ctx_n(ctx)), S.items_open(B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), rel)), d0, d1, l, e),
        e0 => k0(e0, set_keep(part, c, q, Some{False{}}, bq, fre, lq, B.same(c, q), {==})),
        e1 => k1(e1, set_keep(part, c, q, Some{True{}}, bq, fre, lq, B.same(c, q), {==})))

def dfs2_some_keep(todo, part, t, f, ctx, l, e, q, bq, lq):
  match todo:
    case Nil{}:
      leaf_keep(ctx, part, l, q, bq, lq, leaf_some(ctx, S.fill(part), l, S.check(ctx, S.fill(part)), {==}, e))
    case S.Todo{c, rel} <> rest:
      dfs2_some_keep.node(c, rel, rest, part, t, f, ctx, l, q, bq, S.is_none(S.look(part, c)), {==}, e, lq,
        e2 => dfs2_some_keep(rest, part, t, f, ctx, l, e2, q, bq, lq),
        e2 => l2 => dfs2_some_keep(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{False{}}), t, Nat.sub(f, 1n), ctx, l, e2, q, bq, l2),
        e2 => l2 => dfs2_some_keep(rest, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), 1n+t, Nat.sub(f, 1n), ctx, l, e2, q, bq, l2))

# The check is consistency
# ========================

def items_agrees.cell(+w: Nat, +h: Nat, +rows: T.Grid(T.Seen), +layout: T.Grid(Bool), +p: T.Pos,
  +t: List<&2, T.Pos>, +s: T.Seen,
  ih: {S.items_ok(S.items(w, h, rows, t), layout) == L.agrees_all(w, h, rows, layout, t) : Bool}) ->
  {S.items_ok(S.items.put(s, p, w, h, S.items(w, h, rows, t)), layout)
    == Bool.and(L.agrees(w, h, layout, p, s), L.agrees_all(w, h, rows, layout, t)) : Bool}:
  match s:
    case T.Hidden{}:
      ih
    case T.Shown{k}:
      %PC.mine_eq(layout, p) :
        {Bool.and(Bool.and(Bool.not(B.mine(layout, p)), Nat.is_eq(B.count_mines(layout, B.neighbours(w, h, p)), k)),
          S.items_ok(S.items(w, h, rows, t), layout))
          == Bool.and(Bool.and(Bool.not(_), Nat.is_eq(L.adj_mines(w, h, layout, p), k)), L.agrees_all(w, h, rows, layout, t)) : Bool}
      %PC.adj_mines_eq(w, h, layout, p) :
        {Bool.and(Bool.and(Bool.not(B.mine(layout, p)), Nat.is_eq(B.adj_mines(w, h, layout, p), k)),
          S.items_ok(S.items(w, h, rows, t), layout))
          == Bool.and(Bool.and(Bool.not(B.mine(layout, p)), Nat.is_eq(_, k)), L.agrees_all(w, h, rows, layout, t)) : Bool}
      %Equal.sym(Bool, S.items_ok(S.items(w, h, rows, t), layout), L.agrees_all(w, h, rows, layout, t), ih) :
        {Bool.and(Bool.and(Bool.not(B.mine(layout, p)), Nat.is_eq(B.adj_mines(w, h, layout, p), k)), _)
          == Bool.and(Bool.and(Bool.not(B.mine(layout, p)), Nat.is_eq(B.adj_mines(w, h, layout, p), k)), L.agrees_all(w, h, rows, layout, t)) : Bool}
      {==}
    case T.Boom{}:
      %PC.mine_eq(layout, p) :
        {Bool.and(B.mine(layout, p), S.items_ok(S.items(w, h, rows, t), layout))
          == Bool.and(_, L.agrees_all(w, h, rows, layout, t)) : Bool}
      %Equal.sym(Bool, S.items_ok(S.items(w, h, rows, t), layout), L.agrees_all(w, h, rows, layout, t), ih) :
        {Bool.and(B.mine(layout, p), _) == Bool.and(B.mine(layout, p), L.agrees_all(w, h, rows, layout, t)) : Bool}
      {==}

law items_agrees:
  for +w: Nat
  for +h: Nat
  for +rows: T.Grid(T.Seen)
  for +layout: T.Grid(Bool)
  for +ps: List<&2, T.Pos>
  {S.items_ok(S.items(w, h, rows, ps), layout) == L.agrees_all(w, h, rows, layout, ps) : Bool}

def items_agrees(w, h, rows, layout, ps):
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      %PC.at_eq(T.Seen, T.Hidden{}, rows, p) :
        {S.items_ok(S.items.put(B.at(T.Seen, T.Hidden{}, rows, p), p, w, h, S.items(w, h, rows, t)), layout)
          == Bool.and(L.agrees(w, h, layout, p, _), L.agrees_all(w, h, rows, layout, t)) : Bool}
      items_agrees.cell(w, h, rows, layout, p, t, B.at(T.Seen, T.Hidden{}, rows, p), items_agrees(w, h, rows, layout, t))

# The solver's check is LAWS.bend's consistent.
law check_cons:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +layout: T.Grid(Bool)
  {S.check(S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}, layout)
    == L.consistent(T.Knowledge{w, h, n, rows}, layout) : Bool}

def check_cons(w, h, n, rows, layout):
  +its = S.items(w, h, rows, B.cells(w, h))
  %PC.shaped_eq(Bool, w, h, layout) :
    {Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n)),
      S.items_ok(its, layout))
      == Bool.and(Bool.and(Bool.and(_, L.shaped(T.Seen, w, h, rows)), Nat.is_eq(L.total_mines(layout), n)),
        L.agrees_all(w, h, rows, layout, L.cells(w, h))) : Bool}
  %PC.shaped_eq(T.Seen, w, h, rows) :
    {Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n)),
      S.items_ok(its, layout))
      == Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), _), Nat.is_eq(L.total_mines(layout), n)),
        L.agrees_all(w, h, rows, layout, L.cells(w, h))) : Bool}
  %PC.total_mines_eq(layout) :
    {Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n)),
      S.items_ok(its, layout))
      == Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(_, n)),
        L.agrees_all(w, h, rows, layout, L.cells(w, h))) : Bool}
  %PC.cells_eq(w, h) :
    {Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n)),
      S.items_ok(its, layout))
      == Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n)),
        L.agrees_all(w, h, rows, layout, _)) : Bool}
  %items_agrees(w, h, rows, layout, B.cells(w, h)) :
    {Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n)),
      S.items_ok(its, layout))
      == Bool.and(Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n)),
        _) : Bool}
  {==}

# The starting partial layout
# ===========================

law start_rows_get:
  for +g: T.Grid(T.Seen)
  for +y: Nat
  {Maybe.default(&2, List<&2, Maybe<&2, Bool>>, List.get(&2, List<&2, Maybe<&2, Bool>>, S.start(g), y), Nil{})
    == S.start.row(Maybe.default(&2, List<&2, T.Seen>, List.get(&2, List<&2, T.Seen>, g, y), Nil{})) : List<&2, Maybe<&2, Bool>>}

def start_rows_get(g, y):
  match g y:
    case Nil{} _:
      {==}
    case r <> t 0n:
      {==}
    case r <> t 1n+k:
      start_rows_get(t, k)

law start_row_get:
  for +r: List<&2, T.Seen>
  for +x: Nat
  {Maybe.default(&2, Maybe<&2, Bool>, List.get(&2, Maybe<&2, Bool>, S.start.row(r), x), None{})
    == S.start.cell(Maybe.default(&2, T.Seen, List.get(&2, T.Seen, r, x), T.Hidden{})) : Maybe<&2, Bool>}

def start_row_get(r, x):
  match r x:
    case Nil{} _:
      {==}
    case s <> t 0n:
      {==}
    case s <> t 1n+k:
      start_row_get(t, k)

# Each cell starts as the revealed cells fix it.
law start_at:
  for +rows: T.Grid(T.Seen)
  for +q: T.Pos
  {S.look(S.start(rows), q) == S.start.cell(B.at(T.Seen, T.Hidden{}, rows, q)) : Maybe<&2, Bool>}

def start_at(rows, q):
  match q:
    case T.Pos{x, y}:
      %Equal.sym(List<&2, Maybe<&2, Bool>>,
        Maybe.default(&2, List<&2, Maybe<&2, Bool>>, List.get(&2, List<&2, Maybe<&2, Bool>>, S.start(rows), y), Nil{}),
        S.start.row(Maybe.default(&2, List<&2, T.Seen>, List.get(&2, List<&2, T.Seen>, rows, y), Nil{})),
        start_rows_get(rows, y)) :
        {Maybe.default(&2, Maybe<&2, Bool>, List.get(&2, Maybe<&2, Bool>, _, x), None{})
          == S.start.cell(B.at(T.Seen, T.Hidden{}, rows, T.Pos{x, y})) : Maybe<&2, Bool>}
      start_row_get(Maybe.default(&2, List<&2, T.Seen>, List.get(&2, List<&2, T.Seen>, rows, y), Nil{}), x)

law start_row_len:
  for +r: List<&2, T.Seen>
  {List.length(&2, Maybe<&2, Bool>, S.start.row(r)) == List.length(&2, T.Seen, r) : Nat}

def start_row_len(r):
  match r:
    case Nil{}:
      {==}
    case s <> t:
      %Equal.sym(Nat, List.length(&2, Maybe<&2, Bool>, S.start.row(t)), List.length(&2, T.Seen, t), start_row_len(t)) :
        {1n+_ == 1n+List.length(&2, T.Seen, t) : Nat}
      {==}

law start_len:
  for +g: T.Grid(T.Seen)
  {List.length(&2, List<&2, Maybe<&2, Bool>>, S.start(g)) == List.length(&2, List<&2, T.Seen>, g) : Nat}

def start_len(g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %Equal.sym(Nat, List.length(&2, List<&2, Maybe<&2, Bool>>, S.start(t)), List.length(&2, List<&2, T.Seen>, t), start_len(t)) :
        {1n+_ == 1n+List.length(&2, List<&2, T.Seen>, t) : Nat}
      {==}

law start_wide:
  for +w: Nat
  for +g: T.Grid(T.Seen)
  {B.rows_wide(Maybe<&2, Bool>, w, S.start(g)) == B.rows_wide(T.Seen, w, g) : Bool}

def start_wide(w, g):
  match g:
    case Nil{}:
      {==}
    case r <> t:
      %Equal.sym(Nat, List.length(&2, Maybe<&2, Bool>, S.start.row(r)), List.length(&2, T.Seen, r), start_row_len(r)) :
        {Bool.and(Nat.is_eq(_, w), B.rows_wide(Maybe<&2, Bool>, w, S.start(t)))
          == Bool.and(Nat.is_eq(List.length(&2, T.Seen, r), w), B.rows_wide(T.Seen, w, t)) : Bool}
      %Equal.sym(Bool, B.rows_wide(Maybe<&2, Bool>, w, S.start(t)), B.rows_wide(T.Seen, w, t), start_wide(w, t)) :
        {Bool.and(Nat.is_eq(List.length(&2, T.Seen, r), w), _)
          == Bool.and(Nat.is_eq(List.length(&2, T.Seen, r), w), B.rows_wide(T.Seen, w, t)) : Bool}
      {==}

law start_shaped:
  for +w: Nat
  for +h: Nat
  for +g: T.Grid(T.Seen)
  {B.shaped(Maybe<&2, Bool>, w, h, S.start(g)) == B.shaped(T.Seen, w, h, g) : Bool}

def start_shaped(w, h, g):
  %Equal.sym(Nat, List.length(&2, List<&2, Maybe<&2, Bool>>, S.start(g)), List.length(&2, List<&2, T.Seen>, g), start_len(g)) :
    {Bool.and(Nat.is_eq(_, h), B.rows_wide(Maybe<&2, Bool>, w, S.start(g)))
      == Bool.and(Nat.is_eq(List.length(&2, List<&2, T.Seen>, g), h), B.rows_wide(T.Seen, w, g)) : Bool}
  %Equal.sym(Bool, B.rows_wide(Maybe<&2, Bool>, w, S.start(g)), B.rows_wide(T.Seen, w, g), start_wide(w, g)) :
    {Bool.and(Nat.is_eq(List.length(&2, List<&2, T.Seen>, g), h), _)
      == Bool.and(Nat.is_eq(List.length(&2, List<&2, T.Seen>, g), h), B.rows_wide(T.Seen, w, g)) : Bool}
  {==}

def start_comp.cell(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +q: T.Pos, +s: T.Seen,
  ag: {L.agrees(w, h, layout, q, s) == True{} : Bool}) ->
  {cmp_cell(S.start.cell(s), B.mine(layout, q)) == True{} : Bool}:
  match s:
    case T.Hidden{}:
      {==}
    case T.Shown{k}:
      %Equal.sym(Bool, B.mine(layout, q), False{}, P.not_true(B.mine(layout, q),
        %Equal.sym(Bool, B.mine(layout, q), L.mine(layout, q), PC.mine_eq(layout, q)) : {Bool.not(_) == True{} : Bool};
        P.and_true_l(Bool.not(L.mine(layout, q)), Nat.is_eq(L.adj_mines(w, h, layout, q), k), ag))) :
        {beq(_, False{}) == True{} : Bool}
      {==}
    case T.Boom{}:
      %Equal.sym(Bool, B.mine(layout, q), True{},
        %Equal.sym(Bool, B.mine(layout, q), L.mine(layout, q), PC.mine_eq(layout, q)) : {_ == True{} : Bool}; ag) :
        {beq(_, True{}) == True{} : Bool}
      {==}

law start_comp.go:
  for +w: Nat
  for +h: Nat
  for +rows: T.Grid(T.Seen)
  for +layout: T.Grid(Bool)
  for +ps: List<&2, T.Pos>
  for +ag: {L.agrees_all(w, h, rows, layout, ps) == True{} : Bool}
  {PS.allp(~CE, ~cmp_f, CE{S.start(rows), layout}, ps) == True{} : Bool}

def start_comp.go(w, h, rows, layout, ps, ag):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +s = L.at(T.Seen, T.Hidden{}, rows, q)
      +a1 = L.agrees(w, h, layout, q, s)
      %Equal.sym(Bool, cmp_f(CE{S.start(rows), layout}, q), True{},
        %Equal.sym(Maybe<&2, Bool>, S.look(S.start(rows), q), S.start.cell(B.at(T.Seen, T.Hidden{}, rows, q)), start_at(rows, q)) :
          {cmp_cell(_, B.mine(layout, q)) == True{} : Bool};
        %Equal.sym(T.Seen, B.at(T.Seen, T.Hidden{}, rows, q), L.at(T.Seen, T.Hidden{}, rows, q), PC.at_eq(T.Seen, T.Hidden{}, rows, q)) :
          {cmp_cell(S.start.cell(_), B.mine(layout, q)) == True{} : Bool};
        start_comp.cell(w, h, layout, q, s, P.and_true_l(a1, L.agrees_all(w, h, rows, layout, t), ag))) :
        {Bool.and(_, PS.allp(~CE, ~cmp_f, CE{S.start(rows), layout}, t)) == True{} : Bool}
      start_comp.go(w, h, rows, layout, t, P.and_true_r(a1, L.agrees_all(w, h, rows, layout, t), ag))

# A consistent layout completes the starting partial layout.
law start_comp:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +layout: T.Grid(Bool)
  for cons: {L.consistent(T.Knowledge{w, h, n, rows}, layout) == True{} : Bool}
  {completes(w, h, S.start(rows), layout) == True{} : Bool}

def start_comp(w, h, n, rows, layout, cons):
  +a = L.shaped(Bool, w, h, layout)
  +b = L.shaped(T.Seen, w, h, rows)
  +c = Nat.is_eq(L.total_mines(layout), n)
  +d = L.agrees_all(w, h, rows, layout, L.cells(w, h))
  start_comp.go(w, h, rows, layout, B.cells(w, h),
    %Equal.sym(List<&2, T.Pos>, B.cells(w, h), L.cells(w, h), PC.cells_eq(w, h)) :
      {L.agrees_all(w, h, rows, layout, _) == True{} : Bool};
    PW.and4_d(a, b, c, d, cons))

# The items, the to-do list and the hidden cells
# ==============================================

law adj_onb:
  for +w: Nat
  for +h: Nat
  for +s: T.Pos
  for +ns: List<&2, T.Pos>
  for +a: {PS.allp(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, s}, ns) == True{} : Bool}
  {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ns) == True{} : Bool}

def adj_onb(w, h, s, ns, a):
  match ns:
    case Nil{}:
      {==}
    case +q <> +t:
      +hq = PS.allp_head(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, s}, q, t, a)
      %Equal.sym(Bool, B.on_board(w, h, q), True{}, P.and_true_r(B.adjacent(s, q), B.on_board(w, h, q), hq)) :
        {Bool.and(_, PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, t)) == True{} : Bool}
      adj_onb(w, h, s, t, PS.allp_tail(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, s}, q, t, a))

def items_onb.cell(+w: Nat, +h: Nat, +rows: T.Grid(T.Seen), +p: T.Pos, +t: List<&2, T.Pos>, +s: T.Seen,
  on: {B.on_board(w, h, p) == True{} : Bool},
  ih: {items_onb(PS.WH{w, h}, S.items(w, h, rows, t)) == True{} : Bool}) ->
  {items_onb(PS.WH{w, h}, S.items.put(s, p, w, h, S.items(w, h, rows, t))) == True{} : Bool}:
  match s:
    case T.Hidden{}:
      ih
    case T.Shown{k}:
      %Equal.sym(Bool, B.on_board(w, h, p), True{}, on) :
        {Bool.and(Bool.and(_, PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, B.neighbours(w, h, p))),
          items_onb(PS.WH{w, h}, S.items(w, h, rows, t))) == True{} : Bool}
      %Equal.sym(Bool, PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, B.neighbours(w, h, p)), True{},
        adj_onb(w, h, p, B.neighbours(w, h, p), PS.neighbours_all(w, h, p))) :
        {Bool.and(Bool.and(True{}, _), items_onb(PS.WH{w, h}, S.items(w, h, rows, t))) == True{} : Bool}
      ih
    case T.Boom{}:
      %Equal.sym(Bool, B.on_board(w, h, p), True{}, on) :
        {Bool.and(Bool.and(_, True{}), items_onb(PS.WH{w, h}, S.items(w, h, rows, t))) == True{} : Bool}
      ih

law items_onb_all:
  for +w: Nat
  for +h: Nat
  for +rows: T.Grid(T.Seen)
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  {items_onb(PS.WH{w, h}, S.items(w, h, rows, ps)) == True{} : Bool}

def items_onb_all(w, h, rows, ps, ons):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      items_onb.cell(w, h, rows, p, t, B.at(T.Seen, T.Hidden{}, rows, p),
        PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, p, t, ons),
        items_onb_all(w, h, rows, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, p, t, ons)))

def around_ok.cell(+b: Bool, +i: S.Item, +rest: List<&2, S.Item>, +layout: T.Grid(Bool),
  hi: {S.items_ok([i], layout) == True{} : Bool}, hr: {S.items_ok(rest, layout) == True{} : Bool}) ->
  {S.items_ok(List.filter.put(S.Item, i, rest, b), layout) == True{} : Bool}:
  match b:
    case False{}:
      hr
    case True{}:
      match i:
        case S.Item{p, s, ns}:
          %Equal.sym(Bool, S.items_ok(rest, layout), True{}, hr) :
            {Bool.and(S.item_ok(s, p, ns, layout), _) == True{} : Bool}
          hi

law around_ok:
  for +its: List<&2, S.Item>
  for +c: T.Pos
  for +layout: T.Grid(Bool)
  for +ok: {S.items_ok(its, layout) == True{} : Bool}
  {S.items_ok(S.around(its, c), layout) == True{} : Bool}

def around_ok(its, c, layout, ok):
  match its:
    case Nil{}:
      {==}
    case S.Item{p, s, ns} <> t:
      +i = {S.Item{p, s, ns} : S.Item}
      +o1 = S.item_ok(s, p, ns, layout)
      around_ok.cell(S.is_number(s) && B.contains(ns, c), i, S.around(t, c), layout,
        %Equal.sym(Bool, Bool.and(o1, True{}), o1, P.and_true_r_id(o1)) : {_ == True{} : Bool};
          P.and_true_l(o1, S.items_ok(t, layout), ok),
        around_ok(t, c, layout, P.and_true_r(o1, S.items_ok(t, layout), ok)))

def around_onb.cell(+e: PS.WH, +i: S.Item, +rest: List<&2, S.Item>, +b: Bool,
  hi: {item_onb(e, i) == True{} : Bool}, hr: {items_onb(e, rest) == True{} : Bool}) ->
  {items_onb(e, List.filter.put(S.Item, i, rest, b)) == True{} : Bool}:
  match b:
    case False{}:
      hr
    case True{}:
      %Equal.sym(Bool, item_onb(e, i), True{}, hi) : {Bool.and(_, items_onb(e, rest)) == True{} : Bool}
      hr

law around_onb:
  for +e: PS.WH
  for +its: List<&2, S.Item>
  for +c: T.Pos
  for +ok: {items_onb(e, its) == True{} : Bool}
  {items_onb(e, S.around(its, c)) == True{} : Bool}

def around_onb(e, its, c, ok):
  match its:
    case Nil{}:
      {==}
    case S.Item{p, s, ns} <> t:
      +i = {S.Item{p, s, ns} : S.Item}
      around_onb.cell(e, i, S.around(t, c), S.is_number(s) && B.contains(ns, c),
        P.and_true_l(item_onb(e, i), items_onb(e, t), ok),
        around_onb(e, t, c, P.and_true_r(item_onb(e, i), items_onb(e, t), ok)))

law todos_ok_all:
  for +its: List<&2, S.Item>
  for +cs: List<&2, T.Pos>
  for +layout: T.Grid(Bool)
  for +ok: {S.items_ok(its, layout) == True{} : Bool}
  {todos_ok(S.todos(its, cs), layout) == True{} : Bool}

def todos_ok_all(its, cs, layout, ok):
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      %Equal.sym(Bool, S.items_ok(S.around(its, c), layout), True{}, around_ok(its, c, layout, ok)) :
        {Bool.and(_, todos_ok(S.todos(its, t), layout)) == True{} : Bool}
      todos_ok_all(its, t, layout, ok)

law todos_onb_all:
  for +e: PS.WH
  for +its: List<&2, S.Item>
  for +cs: List<&2, T.Pos>
  for +ok: {items_onb(e, its) == True{} : Bool}
  {todos_onb(e, S.todos(its, cs)) == True{} : Bool}

def todos_onb_all(e, its, cs, ok):
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      %Equal.sym(Bool, items_onb(e, S.around(its, c)), True{}, around_onb(e, its, c, ok)) :
        {Bool.and(_, todos_onb(e, S.todos(its, t))) == True{} : Bool}
      todos_onb_all(e, its, t, ok)

def tok_put(+b: Bool, +t: S.Todo, +rest: List<&2, S.Todo>, +layout: T.Grid(Bool),
  ht: {todos_ok([t], layout) == True{} : Bool}, hr: {todos_ok(rest, layout) == True{} : Bool}) ->
  {todos_ok(List.filter.put(S.Todo, t, rest, b), layout) == True{} : Bool}:
  match b:
    case False{}:
      hr
    case True{}:
      match t:
        case S.Todo{c, rel}:
          %Equal.sym(Bool, todos_ok(rest, layout), True{}, hr) : {Bool.and(S.items_ok(rel, layout), _) == True{} : Bool}
          ht

def ton_put(+b: Bool, +e: PS.WH, +t: S.Todo, +rest: List<&2, S.Todo>,
  ht: {todos_onb(e, [t]) == True{} : Bool}, hr: {todos_onb(e, rest) == True{} : Bool}) ->
  {todos_onb(e, List.filter.put(S.Todo, t, rest, b)) == True{} : Bool}:
  match b:
    case False{}:
      hr
    case True{}:
      match t:
        case S.Todo{c, rel}:
          %Equal.sym(Bool, todos_onb(e, rest), True{}, hr) : {Bool.and(items_onb(e, rel), _) == True{} : Bool}
          ht

law tok_append:
  for +xs: List<&2, S.Todo>
  for +ys: List<&2, S.Todo>
  for +layout: T.Grid(Bool)
  for +a: {todos_ok(xs, layout) == True{} : Bool}
  for b: {todos_ok(ys, layout) == True{} : Bool}
  {todos_ok(List.append(&2, S.Todo, xs, ys), layout) == True{} : Bool}

def tok_append(xs, ys, layout, a, b):
  match xs:
    case Nil{}:
      b
    case S.Todo{c, rel} <> t:
      %Equal.sym(Bool, S.items_ok(rel, layout), True{}, P.and_true_l(S.items_ok(rel, layout), todos_ok(t, layout), a)) :
        {Bool.and(_, todos_ok(List.append(&2, S.Todo, t, ys), layout)) == True{} : Bool}
      tok_append(t, ys, layout, P.and_true_r(S.items_ok(rel, layout), todos_ok(t, layout), a), b)

law ton_append:
  for +e: PS.WH
  for +xs: List<&2, S.Todo>
  for +ys: List<&2, S.Todo>
  for +a: {todos_onb(e, xs) == True{} : Bool}
  for b: {todos_onb(e, ys) == True{} : Bool}
  {todos_onb(e, List.append(&2, S.Todo, xs, ys)) == True{} : Bool}

def ton_append(e, xs, ys, a, b):
  match xs:
    case Nil{}:
      b
    case S.Todo{c, rel} <> t:
      %Equal.sym(Bool, items_onb(e, rel), True{}, P.and_true_l(items_onb(e, rel), todos_onb(e, t), a)) :
        {Bool.and(_, todos_onb(e, List.append(&2, S.Todo, t, ys))) == True{} : Bool}
      ton_append(e, t, ys, P.and_true_r(items_onb(e, rel), todos_onb(e, t), a), b)

def tok_head(+t: S.Todo, +rest: List<&2, S.Todo>, +layout: T.Grid(Bool),
  h: {todos_ok(t <> rest, layout) == True{} : Bool}) -> {todos_ok([t], layout) == True{} : Bool}:
  match t:
    case S.Todo{c, rel}:
      %Equal.sym(Bool, Bool.and(S.items_ok(rel, layout), True{}), S.items_ok(rel, layout), P.and_true_r_id(S.items_ok(rel, layout))) :
        {_ == True{} : Bool}
      P.and_true_l(S.items_ok(rel, layout), todos_ok(rest, layout), h)

def tok_tail(+t: S.Todo, +rest: List<&2, S.Todo>, +layout: T.Grid(Bool),
  h: {todos_ok(t <> rest, layout) == True{} : Bool}) -> {todos_ok(rest, layout) == True{} : Bool}:
  match t:
    case S.Todo{c, rel}:
      P.and_true_r(S.items_ok(rel, layout), todos_ok(rest, layout), h)

def ton_head(+e: PS.WH, +t: S.Todo, +rest: List<&2, S.Todo>,
  h: {todos_onb(e, t <> rest) == True{} : Bool}) -> {todos_onb(e, [t]) == True{} : Bool}:
  match t:
    case S.Todo{c, rel}:
      %Equal.sym(Bool, Bool.and(items_onb(e, rel), True{}), items_onb(e, rel), P.and_true_r_id(items_onb(e, rel))) :
        {_ == True{} : Bool}
      P.and_true_l(items_onb(e, rel), todos_onb(e, rest), h)

def ton_tail(+e: PS.WH, +t: S.Todo, +rest: List<&2, S.Todo>,
  h: {todos_onb(e, t <> rest) == True{} : Bool}) -> {todos_onb(e, rest) == True{} : Bool}:
  match t:
    case S.Todo{c, rel}:
      P.and_true_r(items_onb(e, rel), todos_onb(e, rest), h)

law tok_order:
  for +ts: List<&2, S.Todo>
  for +layout: T.Grid(Bool)
  for +h: {todos_ok(ts, layout) == True{} : Bool}
  {todos_ok(S.nears(ts), layout) == True{} : Bool}

def tok_order(ts, layout, h):
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      tok_put(S.has_rel(t), t, S.nears(rest), layout, tok_head(t, rest, layout, h),
        tok_order(rest, layout, tok_tail(t, rest, layout, h)))

law tok_order_f:
  for +ts: List<&2, S.Todo>
  for +layout: T.Grid(Bool)
  for +h: {todos_ok(ts, layout) == True{} : Bool}
  {todos_ok(S.fars(ts), layout) == True{} : Bool}

def tok_order_f(ts, layout, h):
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      tok_put(Bool.not(S.has_rel(t)), t, S.fars(rest), layout, tok_head(t, rest, layout, h),
        tok_order_f(rest, layout, tok_tail(t, rest, layout, h)))

law ton_order:
  for +e: PS.WH
  for +ts: List<&2, S.Todo>
  for +h: {todos_onb(e, ts) == True{} : Bool}
  {todos_onb(e, S.nears(ts)) == True{} : Bool}

def ton_order(e, ts, h):
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      ton_put(S.has_rel(t), e, t, S.nears(rest), ton_head(e, t, rest, h), ton_order(e, rest, ton_tail(e, t, rest, h)))

law ton_order_f:
  for +e: PS.WH
  for +ts: List<&2, S.Todo>
  for +h: {todos_onb(e, ts) == True{} : Bool}
  {todos_onb(e, S.fars(ts)) == True{} : Bool}

def ton_order_f(e, ts, h):
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      ton_put(Bool.not(S.has_rel(t)), e, t, S.fars(rest), ton_head(e, t, rest, h), ton_order_f(e, rest, ton_tail(e, t, rest, h)))

law tcontains_todos:
  for +its: List<&2, S.Item>
  for +cs: List<&2, T.Pos>
  for +q: T.Pos
  {tcontains(S.todos(its, cs), q) == B.contains(cs, q) : Bool}

def tcontains_todos(its, cs, q):
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      %tcontains_todos(its, t, q) : {Bool.or(B.same(c, q), tcontains(S.todos(its, t), q)) == Bool.or(B.same(c, q), _) : Bool}
      {==}

def tput_keeps(+b: Bool, +t: S.Todo, +rest: List<&2, S.Todo>, +q: T.Pos, m: {tcontains(rest, q) == True{} : Bool}) ->
  {tcontains(List.filter.put(S.Todo, t, rest, b), q) == True{} : Bool}:
  match b:
    case False{}:
      m
    case True{}:
      match t:
        case S.Todo{c, rel}:
          %Equal.sym(Bool, tcontains(rest, q), True{}, m) : {Bool.or(B.same(c, q), _) == True{} : Bool}
          PS.or_true_r(B.same(c, q))

def tput_self(+b: Bool, +c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +q: T.Pos,
  bt: {b == True{} : Bool}, cq: {B.same(c, q) == True{} : Bool}) ->
  {tcontains(List.filter.put(S.Todo, S.Todo{c, rel}, rest, b), q) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, B.same(c, q), True{}, cq) : {Bool.or(_, tcontains(rest, q)) == True{} : Bool}
      {==}
    case False{}:
      Empty.absurd({tcontains(rest, q) == True{} : Bool}, P.false_ne_true(bt))

def or_l(+a: Bool, +b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

def or_r(+a: Bool, +b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, e) : {Bool.or(a, _) == True{} : Bool}
  PS.or_true_r(a)

def or_cases(+a: Bool, +b: Bool, e: {Bool.or(a, b) == True{} : Bool}) -> Or({a == True{} : Bool}, {b == True{} : Bool}):
  match a:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{e}

def order_split.self(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +q: T.Pos,
  cq: {B.same(c, q) == True{} : Bool}, +hr: Bool, hre: {S.has_rel(S.Todo{c, rel}) == hr : Bool}) ->
  {Bool.or(tcontains(List.filter.put(S.Todo, S.Todo{c, rel}, S.nears(rest), hr), q),
    tcontains(List.filter.put(S.Todo, S.Todo{c, rel}, S.fars(rest), Bool.not(hr)), q)) == True{} : Bool}:
  match hr:
    case True{}:
      or_l(tcontains(List.filter.put(S.Todo, S.Todo{c, rel}, S.nears(rest), True{}), q),
        tcontains(List.filter.put(S.Todo, S.Todo{c, rel}, S.fars(rest), False{}), q),
        tput_self(True{}, c, rel, S.nears(rest), q, {==}, cq))
    case False{}:
      or_r(tcontains(List.filter.put(S.Todo, S.Todo{c, rel}, S.nears(rest), False{}), q),
        tcontains(List.filter.put(S.Todo, S.Todo{c, rel}, S.fars(rest), True{}), q),
        tput_self(True{}, c, rel, S.fars(rest), q, {==}, cq))

def order_split.rest(+t: S.Todo, +rest: List<&2, S.Todo>, +q: T.Pos, +hr: Bool,
  r: Or({tcontains(S.nears(rest), q) == True{} : Bool}, {tcontains(S.fars(rest), q) == True{} : Bool})) ->
  {Bool.or(tcontains(List.filter.put(S.Todo, t, S.nears(rest), hr), q),
    tcontains(List.filter.put(S.Todo, t, S.fars(rest), Bool.not(hr)), q)) == True{} : Bool}:
  match r:
    case Inl{a}:
      or_l(tcontains(List.filter.put(S.Todo, t, S.nears(rest), hr), q),
        tcontains(List.filter.put(S.Todo, t, S.fars(rest), Bool.not(hr)), q), tput_keeps(hr, t, S.nears(rest), q, a))
    case Inr{b}:
      or_r(tcontains(List.filter.put(S.Todo, t, S.nears(rest), hr), q),
        tcontains(List.filter.put(S.Todo, t, S.fars(rest), Bool.not(hr)), q), tput_keeps(Bool.not(hr), t, S.fars(rest), q, b))

def order_split.cell(+c: T.Pos, +rel: List<&2, S.Item>, +rest: List<&2, S.Todo>, +q: T.Pos,
  r: Or({B.same(c, q) == True{} : Bool}, {tcontains(rest, q) == True{} : Bool}),
  ih: {tcontains(rest, q) == True{} : Bool} ->
    {Bool.or(tcontains(S.nears(rest), q), tcontains(S.fars(rest), q)) == True{} : Bool}) ->
  {Bool.or(tcontains(S.nears(S.Todo{c, rel} <> rest), q), tcontains(S.fars(S.Todo{c, rel} <> rest), q)) == True{} : Bool}:
  match r:
    case Inl{cq}:
      order_split.self(c, rel, rest, q, cq, S.has_rel(S.Todo{c, rel}), {==})
    case Inr{m}:
      order_split.rest(S.Todo{c, rel}, rest, q, S.has_rel(S.Todo{c, rel}),
        or_cases(tcontains(S.nears(rest), q), tcontains(S.fars(rest), q), ih(m)))

# A to-do cell is in the near part or the far part.
law order_split:
  for +ts: List<&2, S.Todo>
  for +q: T.Pos
  for m: {tcontains(ts, q) == True{} : Bool}
  {Bool.or(tcontains(S.nears(ts), q), tcontains(S.fars(ts), q)) == True{} : Bool}

def order_split(ts, q, m):
  match ts:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, P.false_ne_true(m))
    case S.Todo{c, rel} <> rest:
      order_split.cell(c, rel, rest, q, or_cases(B.same(c, q), tcontains(rest, q), m), mr => order_split(rest, q, mr))

law tcontains_append:
  for +xs: List<&2, S.Todo>
  for +ys: List<&2, S.Todo>
  for +q: T.Pos
  {tcontains(List.append(&2, S.Todo, xs, ys), q) == Bool.or(tcontains(xs, q), tcontains(ys, q)) : Bool}

def tcontains_append(xs, ys, q):
  match xs:
    case Nil{}:
      {==}
    case S.Todo{c, rel} <> t:
      %Equal.sym(Bool, tcontains(List.append(&2, S.Todo, t, ys), q), Bool.or(tcontains(t, q), tcontains(ys, q)),
        tcontains_append(t, ys, q)) :
        {Bool.or(B.same(c, q), _) == Bool.or(Bool.or(B.same(c, q), tcontains(t, q)), tcontains(ys, q)) : Bool}
      PS.contains_append.or(B.same(c, q), tcontains(t, q), tcontains(ys, q))

law order_member:
  for +ts: List<&2, S.Todo>
  for +q: T.Pos
  for m: {tcontains(ts, q) == True{} : Bool}
  {tcontains(S.order(ts), q) == True{} : Bool}

def order_member(ts, q, m):
  %Equal.sym(Bool, tcontains(List.append(&2, S.Todo, S.nears(ts), S.fars(ts)), q),
    Bool.or(tcontains(S.nears(ts), q), tcontains(S.fars(ts), q)), tcontains_append(S.nears(ts), S.fars(ts), q)) :
    {_ == True{} : Bool}
  order_split(ts, q, m)

def hc_member.go(+rows: T.Grid(T.Seen), +p: T.Pos, +t: List<&2, T.Pos>, +q: T.Pos,
  hq: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool},
  r: Or({B.same(p, q) == True{} : Bool}, {B.contains(t, q) == True{} : Bool}),
  ih: {B.contains(t, q) == True{} : Bool} -> {B.contains(S.hidden_cells(rows, t), q) == True{} : Bool}) ->
  {B.contains(S.hidden_cells(rows, p <> t), q) == True{} : Bool}:
  match r:
    case Inl{pq}:
      %Equal.sym(T.Pos, p, q, PG.same_sound(p, q, pq)) :
        {B.contains(List.filter.put(T.Pos, _, S.hidden_cells(rows, t), S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, _))), q) == True{} : Bool}
      %Equal.sym(Bool, S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)), True{}, hq) :
        {B.contains(List.filter.put(T.Pos, q, S.hidden_cells(rows, t), _), q) == True{} : Bool}
      PG.contains_cons_self(q, S.hidden_cells(rows, t))
    case Inr{m}:
      PS.put_keeps(p, S.hidden_cells(rows, t), S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)), q, ih(m))

# A hidden cell of ps is one of the hidden cells.
law hc_member:
  for +rows: T.Grid(T.Seen)
  for +ps: List<&2, T.Pos>
  for +q: T.Pos
  for m: {B.contains(ps, q) == True{} : Bool}
  for +hq: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool}
  {B.contains(S.hidden_cells(rows, ps), q) == True{} : Bool}

def hc_member(rows, ps, q, m, hq):
  match ps:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, P.false_ne_true(m))
    case p <> t:
      hc_member.go(rows, p, t, q, hq, or_cases(B.same(p, q), B.contains(t, q), m), mt => hc_member(rows, t, q, mt, hq))

def hc_sound.f(+rows: T.Grid(T.Seen), +p: T.Pos, +t: List<&2, T.Pos>, +q: T.Pos,
  r: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(t, q) == True{} : Bool}) ->
  {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(p <> t, q) == True{} : Bool}:
  match r:
    case (a, b):
      (a, or_r(B.same(p, q), B.contains(t, q), b))

def hc_sound.t(+rows: T.Grid(T.Seen), +p: T.Pos, +t: List<&2, T.Pos>, +q: T.Pos,
  be: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)) == True{} : Bool},
  r: Or({B.same(p, q) == True{} : Bool}, {B.contains(S.hidden_cells(rows, t), q) == True{} : Bool}),
  ih: {B.contains(S.hidden_cells(rows, t), q) == True{} : Bool} ->
    {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(t, q) == True{} : Bool}) ->
  {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(p <> t, q) == True{} : Bool}:
  match r:
    case Inl{+pq}:
      (%PG.same_sound(p, q, pq) : {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, _)) == True{} : Bool}; be,
        or_l(B.same(p, q), B.contains(t, q), pq))
    case Inr{m}:
      hc_sound.f(rows, p, t, q, ih(m))

def hc_sound.go(+rows: T.Grid(T.Seen), +p: T.Pos, +t: List<&2, T.Pos>, +q: T.Pos, +b: Bool,
  be: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)) == b : Bool},
  m: {B.contains(List.filter.put(T.Pos, p, S.hidden_cells(rows, t), b), q) == True{} : Bool},
  ih: {B.contains(S.hidden_cells(rows, t), q) == True{} : Bool} ->
    {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(t, q) == True{} : Bool}) ->
  {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(p <> t, q) == True{} : Bool}:
  match b:
    case True{}:
      hc_sound.t(rows, p, t, q, be, or_cases(B.same(p, q), B.contains(S.hidden_cells(rows, t), q), m), ih)
    case False{}:
      hc_sound.f(rows, p, t, q, ih(m))

# A hidden cell is hidden and one of the cells it was taken from.
law hc_sound:
  for +rows: T.Grid(T.Seen)
  for +ps: List<&2, T.Pos>
  for +q: T.Pos
  for m: {B.contains(S.hidden_cells(rows, ps), q) == True{} : Bool}
  {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(ps, q) == True{} : Bool}

def hc_sound(rows, ps, q, m):
  match ps:
    case Nil{}:
      Empty.absurd({S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, q)) == True{} : Bool} & {B.contains(Nil{}, q) == True{} : Bool},
        P.false_ne_true(m))
    case p <> t:
      hc_sound.go(rows, p, t, q, S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)), {==}, m, mt => hc_sound(rows, t, q, mt))

# The search's start
# ==================

def start_cover.seen(+w: Nat, +h: Nat, +rows: T.Grid(T.Seen), +its: List<&2, S.Item>, +q: T.Pos,
  on: {B.on_board(w, h, q) == True{} : Bool}, +s: T.Seen, se: {B.at(T.Seen, T.Hidden{}, rows, q) == s : T.Seen}) ->
  {Bool.or(Bool.not(S.is_none(S.start.cell(s))), tcontains(S.order(S.todos(its, S.hidden_cells(rows, B.cells(w, h)))), q))
    == True{} : Bool}:
  match s:
    case T.Hidden{}:
      +hs = S.hidden_cells(rows, B.cells(w, h))
      order_member(S.todos(its, hs), q,
        %Equal.sym(Bool, tcontains(S.todos(its, hs), q), B.contains(hs, q), tcontains_todos(its, hs, q)) : {_ == True{} : Bool};
        hc_member(rows, B.cells(w, h), q, PS.cells_member(w, h, q, on),
          %Equal.sym(T.Seen, B.at(T.Seen, T.Hidden{}, rows, q), T.Hidden{}, se) : {S.is_hidden(_) == True{} : Bool}; {==}))
    case T.Shown{k}:
      {==}
    case T.Boom{}:
      {==}

def start_cover.cell(+w: Nat, +h: Nat, +rows: T.Grid(T.Seen), +its: List<&2, S.Item>, +c: T.Pos, +q: T.Pos,
  +shP: {B.shaped(Maybe<&2, Bool>, w, h, S.start(rows)) == True{} : Bool},
  on: {B.on_board(w, h, q) == True{} : Bool}, +b: Bool, be: {B.same(c, q) == b : Bool}) ->
  {cv_f(CV{S.order(S.todos(its, S.hidden_cells(rows, B.cells(w, h)))), B.set_at(Maybe<&2, Bool>, S.start(rows), c, Some{True{}})}, q)
    == True{} : Bool}:
  match b:
    case True{}:
      +todo = S.order(S.todos(its, S.hidden_cells(rows, B.cells(w, h))))
      %Equal.sym(T.Pos, c, q, PG.same_sound(c, q, be)) :
        {Bool.or(Bool.not(S.is_none(S.look(B.set_at(Maybe<&2, Bool>, S.start(rows), _, Some{True{}}), q))), tcontains(todo, q)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Bool>, S.look(B.set_at(Maybe<&2, Bool>, S.start(rows), q, Some{True{}}), q), Some{True{}},
        set_look(w, h, S.start(rows), q, Some{True{}}, shP, on)) :
        {Bool.or(Bool.not(S.is_none(_)), tcontains(todo, q)) == True{} : Bool}
      {==}
    case False{}:
      +todo = S.order(S.todos(its, S.hidden_cells(rows, B.cells(w, h))))
      %Equal.sym(Maybe<&2, Bool>, S.look(B.set_at(Maybe<&2, Bool>, S.start(rows), c, Some{True{}}), q), S.look(S.start(rows), q),
        PL.at_set_ne(Maybe<&2, Bool>, S.start(rows), c, q, Some{True{}}, None{}, be)) :
        {Bool.or(Bool.not(S.is_none(_)), tcontains(todo, q)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Bool>, S.look(S.start(rows), q), S.start.cell(B.at(T.Seen, T.Hidden{}, rows, q)), start_at(rows, q)) :
        {Bool.or(Bool.not(S.is_none(_)), tcontains(todo, q)) == True{} : Bool}
      start_cover.seen(w, h, rows, its, q, on, B.at(T.Seen, T.Hidden{}, rows, q), {==})

law start_cover.go:
  for +w: Nat
  for +h: Nat
  for +rows: T.Grid(T.Seen)
  for +its: List<&2, S.Item>
  for +c: T.Pos
  for +shP: {B.shaped(Maybe<&2, Bool>, w, h, S.start(rows)) == True{} : Bool}
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  {PS.allp(~CV, ~cv_f, CV{S.order(S.todos(its, S.hidden_cells(rows, B.cells(w, h)))),
    B.set_at(Maybe<&2, Bool>, S.start(rows), c, Some{True{}})}, ps) == True{} : Bool}

def start_cover.go(w, h, rows, its, c, shP, ps, ons):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +e0 = {CV{S.order(S.todos(its, S.hidden_cells(rows, B.cells(w, h)))), B.set_at(Maybe<&2, Bool>, S.start(rows), c, Some{True{}})} : CV}
      %Equal.sym(Bool, cv_f(e0, q), True{},
        start_cover.cell(w, h, rows, its, c, q, shP, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons), B.same(c, q), {==})) :
        {Bool.and(_, PS.allp(~CV, ~cv_f, e0, t)) == True{} : Bool}
      start_cover.go(w, h, rows, its, c, shP, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))

# The outer loop
# ==============

def all_valid(+ctx: S.Ctx, ls: List<&2, T.Grid(Bool)>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case l <> t:
      S.check(ctx, l) && all_valid(ctx, t)

# A layout that passes the check and mines c.
def Witness(+ctx: S.Ctx, +c: T.Pos) -> Type:
  Exists(T.Grid(Bool), l => {S.check(ctx, l) == True{} : Bool} & {B.mine(l, c) == True{} : Bool})

def covered_extract.go(+ctx: S.Ctx, +l: T.Grid(Bool), +t: List<&2, T.Grid(Bool)>, +c: T.Pos,
  +vl: {S.check(ctx, l) == True{} : Bool},
  r: Or({B.mine(l, c) == True{} : Bool}, {S.covered(t, c) == True{} : Bool}),
  ih: {S.covered(t, c) == True{} : Bool} -> Witness(ctx, c)) -> Witness(ctx, c):
  match r:
    case Inl{m}:
      (l, (vl, m))
    case Inr{cv}:
      ih(cv)

law covered_extract:
  for +ctx: S.Ctx
  for +ls: List<&2, T.Grid(Bool)>
  for +c: T.Pos
  for cov: {S.covered(ls, c) == True{} : Bool}
  for +val: {all_valid(ctx, ls) == True{} : Bool}
  Witness(ctx, c)

def covered_extract(ctx, ls, c, cov, val):
  match ls:
    case Nil{}:
      Empty.absurd(Witness(ctx, c), P.false_ne_true(cov))
    case l <> t:
      covered_extract.go(ctx, l, t, c, P.and_true_l(S.check(ctx, l), all_valid(ctx, t), val),
        or_cases(B.mine(l, c), S.covered(t, c), cov),
        ct => covered_extract(ctx, t, c, ct, P.and_true_r(S.check(ctx, l), all_valid(ctx, t), val)))

def loop_found_some(r: Maybe<&2, T.Grid(Bool)>, +c0: T.Pos, k: T.Grid(Bool) -> Maybe<&2, T.Pos>, +c: T.Pos,
  e: {S.loop.found(r, c0, k) == Some{c} : Maybe<&2, T.Pos>}) ->
  Or({c0 == c : T.Pos} & {r == None{} : Maybe<&2, T.Grid(Bool)>},
    Exists(T.Grid(Bool), l => {r == Some{l} : Maybe<&2, T.Grid(Bool)>} & {k(l) == Some{c} : Maybe<&2, T.Pos>})):
  match r:
    case None{}:
      Inl{(PL.some_inj(T.Pos, c0, c, e), {==})}
    case Some{l}:
      Inr{(l, ({==}, e))}

def LoopSome(+hs: List<&2, T.Pos>, +todo: S.Plan, +part: T.Grid(Maybe<&2, Bool>), +ctx: S.Ctx, +c: T.Pos) -> Type:
  {B.contains(hs, c) == True{} : Bool} & {S.search(c, todo, part, ctx) == None{} : Maybe<&2, T.Grid(Bool)>}

def loop_some.lift(+c0: T.Pos, +t: List<&2, T.Pos>, +todo: S.Plan, +part: T.Grid(Maybe<&2, Bool>),
  +ctx: S.Ctx, +c: T.Pos, r: LoopSome(t, todo, part, ctx, c)) -> LoopSome(c0 <> t, todo, part, ctx, c):
  match r:
    case (m, s):
      (or_r(B.same(c0, c), B.contains(t, c), m), s)

def loop_some.found(+c0: T.Pos, +t: List<&2, T.Pos>, +found: List<&2, T.Grid(Bool)>, +todo: S.Plan,
  +part: T.Grid(Maybe<&2, Bool>), +ctx: S.Ctx, +c: T.Pos,
  r: Or({c0 == c : T.Pos} & {S.search(c0, todo, part, ctx) == None{} : Maybe<&2, T.Grid(Bool)>},
    Exists(T.Grid(Bool), l => {S.search(c0, todo, part, ctx) == Some{l} : Maybe<&2, T.Grid(Bool)>} &
      {S.loop(t, l <> found, todo, part, ctx) == Some{c} : Maybe<&2, T.Pos>})),
  ih: @l: T.Grid(Bool) -> {S.loop(t, l <> found, todo, part, ctx) == Some{c} : Maybe<&2, T.Pos>} -> LoopSome(t, todo, part, ctx, c)) ->
  LoopSome(c0 <> t, todo, part, ctx, c):
  match r:
    case Inl{pr}:
      match pr:
        case (cc, sn):
          %cc : {Bool.or(B.same(c0, _), B.contains(t, _)) == True{} : Bool} &
            {S.search(_, todo, part, ctx) == None{} : Maybe<&2, T.Grid(Bool)>}
          (or_l(B.same(c0, c0), B.contains(t, c0), PG.same_refl(c0)), sn)
    case Inr{ex}:
      match ex:
        case (l, pr):
          match pr:
            case (sl, lp):
              loop_some.lift(c0, t, todo, part, ctx, c, ih(l, lp))

def loop_some.cov(+c0: T.Pos, +t: List<&2, T.Pos>, +found: List<&2, T.Grid(Bool)>, +todo: S.Plan,
  +part: T.Grid(Maybe<&2, Bool>), +ctx: S.Ctx, +c: T.Pos, +b: Bool,
  e: {S.loop.if(b, u => S.loop(t, found, todo, part, ctx),
      v => S.loop.found(S.search(c0, todo, part, ctx), c0, l => S.loop(t, l <> found, todo, part, ctx))) == Some{c} : Maybe<&2, T.Pos>},
  ihf: {S.loop(t, found, todo, part, ctx) == Some{c} : Maybe<&2, T.Pos>} -> LoopSome(t, todo, part, ctx, c),
  ihn: @l: T.Grid(Bool) -> {S.loop(t, l <> found, todo, part, ctx) == Some{c} : Maybe<&2, T.Pos>} -> LoopSome(t, todo, part, ctx, c)) ->
  LoopSome(c0 <> t, todo, part, ctx, c):
  match b:
    case True{}:
      loop_some.lift(c0, t, todo, part, ctx, c, ihf(e))
    case False{}:
      loop_some.found(c0, t, found, todo, part, ctx, c,
        loop_found_some(S.search(c0, todo, part, ctx), c0, l => S.loop(t, l <> found, todo, part, ctx), c, e), ihn)

# When the loop names c, c is one of its cells and its search found nothing.
law loop_some:
  for +hs: List<&2, T.Pos>
  for +found: List<&2, T.Grid(Bool)>
  for +todo: S.Plan
  for +part: T.Grid(Maybe<&2, Bool>)
  for +ctx: S.Ctx
  for +c: T.Pos
  for e: {S.loop(hs, found, todo, part, ctx) == Some{c} : Maybe<&2, T.Pos>}
  LoopSome(hs, todo, part, ctx, c)

def loop_some(hs, found, todo, part, ctx, c, e):
  match hs:
    case Nil{}:
      Empty.absurd(LoopSome(Nil{}, todo, part, ctx, c), PL.none_ne_some(T.Pos, c, e))
    case c0 <> t:
      loop_some.cov(c0, t, found, todo, part, ctx, c, S.covered(found, c0), e,
        ef => loop_some(t, found, todo, part, ctx, c, ef),
        l => el => loop_some(t, l <> found, todo, part, ctx, c, el))

def loop_found_none(r: Maybe<&2, T.Grid(Bool)>, +c0: T.Pos, k: T.Grid(Bool) -> Maybe<&2, T.Pos>,
  e: {S.loop.found(r, c0, k) == None{} : Maybe<&2, T.Pos>}) ->
  Exists(T.Grid(Bool), l => {r == Some{l} : Maybe<&2, T.Grid(Bool)>} & {k(l) == None{} : Maybe<&2, T.Pos>}):
  match r:
    case None{}:
      Empty.absurd(Exists(T.Grid(Bool), l => {None{} == Some{l} : Maybe<&2, T.Grid(Bool)>} & {k(l) == None{} : Maybe<&2, T.Pos>}),
        some_ne_none(T.Pos, c0, e))
    case Some{l}:
      (l, ({==}, e))

def witness_move(+ctx: S.Ctx, +c0: T.Pos, +c: T.Pos, cq: {B.same(c0, c) == True{} : Bool}, wt: Witness(ctx, c0)) ->
  Witness(ctx, c):
  %PG.same_sound(c0, c, cq) : Witness(ctx, _)
  wt

def loop_none.pick(+ctx: S.Ctx, +c0: T.Pos, +t: List<&2, T.Pos>, +c: T.Pos, +l: T.Grid(Bool),
  vl: {S.check(ctx, l) == True{} : Bool}, ml: {B.mine(l, c0) == True{} : Bool},
  mr: Or({B.same(c0, c) == True{} : Bool}, {B.contains(t, c) == True{} : Bool}),
  k: {B.contains(t, c) == True{} : Bool} -> Witness(ctx, c)) -> Witness(ctx, c):
  match mr:
    case Inl{cq}:
      witness_move(ctx, c0, c, cq, (l, (vl, ml)))
    case Inr{mt}:
      k(mt)

def loop_none.found(+c0: T.Pos, +t: List<&2, T.Pos>, +found: List<&2, T.Grid(Bool)>, +todo: S.Plan,
  +part: T.Grid(Maybe<&2, Bool>), +w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +its: List<&2, S.Item>,
  +val: {all_valid(S.Ctx{w, h, n, rows, its}, found) == True{} : Bool},
  +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, on0: {B.on_board(w, h, c0) == True{} : Bool},
  +c: T.Pos, mr: Or({B.same(c0, c) == True{} : Bool}, {B.contains(t, c) == True{} : Bool}),
  ex: Exists(T.Grid(Bool), l => {S.search(c0, todo, part, S.Ctx{w, h, n, rows, its}) == Some{l} : Maybe<&2, T.Grid(Bool)>} &
    {S.loop(t, l <> found, todo, part, S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Pos>}),
  ih: @l: T.Grid(Bool) -> {S.loop(t, l <> found, todo, part, S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Pos>} ->
    {all_valid(S.Ctx{w, h, n, rows, its}, l <> found) == True{} : Bool} -> {B.contains(t, c) == True{} : Bool} ->
    Witness(S.Ctx{w, h, n, rows, its}, c)) ->
  Witness(S.Ctx{w, h, n, rows, its}, c):
  match ex:
    case (+l, pr):
      match pr:
        case (+sl, ln):
          +ctx = {S.Ctx{w, h, n, rows, its} : S.Ctx}
          +p1 = B.set_at(Maybe<&2, Bool>, part, c0, Some{True{}})
          +vl = dfs2_some_check(S.plan_todo(c0, todo, ctx), p1, S.part_true(p1), S.part_none(p1), ctx, l, sl)
          +ml = dfs2_some_keep(S.plan_todo(c0, todo, ctx), p1, S.part_true(p1), S.part_none(p1), ctx, l, sl, c0, True{},
            set_look(w, h, part, c0, Some{True{}}, shP, on0))
          loop_none.pick(ctx, c0, t, c, l, vl, ml, mr,
            mt => ih(l, ln, %Equal.sym(Bool, S.check(ctx, l), True{}, vl) : {Bool.and(_, all_valid(ctx, found)) == True{} : Bool}; val, mt))

def loop_none.pick2(+ctx: S.Ctx, +c0: T.Pos, +t: List<&2, T.Pos>, +c: T.Pos, +found: List<&2, T.Grid(Bool)>,
  mr: Or({B.same(c0, c) == True{} : Bool}, {B.contains(t, c) == True{} : Bool}),
  cov: {S.covered(found, c0) == True{} : Bool}, val: {all_valid(ctx, found) == True{} : Bool},
  k: {B.contains(t, c) == True{} : Bool} -> Witness(ctx, c)) -> Witness(ctx, c):
  match mr:
    case Inl{cq}:
      witness_move(ctx, c0, c, cq, covered_extract(ctx, found, c0, cov, val))
    case Inr{mt}:
      k(mt)

def loop_none.cov(+c0: T.Pos, +t: List<&2, T.Pos>, +found: List<&2, T.Grid(Bool)>, +todo: S.Plan,
  +part: T.Grid(Maybe<&2, Bool>), +w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +its: List<&2, S.Item>,
  +val: {all_valid(S.Ctx{w, h, n, rows, its}, found) == True{} : Bool},
  +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}, on0: {B.on_board(w, h, c0) == True{} : Bool},
  +c: T.Pos, mr: Or({B.same(c0, c) == True{} : Bool}, {B.contains(t, c) == True{} : Bool}),
  +b: Bool, be: {S.covered(found, c0) == b : Bool},
  e: {S.loop.if(b, u => S.loop(t, found, todo, part, S.Ctx{w, h, n, rows, its}),
      v => S.loop.found(S.search(c0, todo, part, S.Ctx{w, h, n, rows, its}), c0,
        l => S.loop(t, l <> found, todo, part, S.Ctx{w, h, n, rows, its}))) == None{} : Maybe<&2, T.Pos>},
  ihf: {S.loop(t, found, todo, part, S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Pos>} ->
    {B.contains(t, c) == True{} : Bool} -> Witness(S.Ctx{w, h, n, rows, its}, c),
  ihn: @l: T.Grid(Bool) -> {S.loop(t, l <> found, todo, part, S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Pos>} ->
    {all_valid(S.Ctx{w, h, n, rows, its}, l <> found) == True{} : Bool} -> {B.contains(t, c) == True{} : Bool} ->
    Witness(S.Ctx{w, h, n, rows, its}, c)) ->
  Witness(S.Ctx{w, h, n, rows, its}, c):
  match b:
    case True{}:
      +ctx = {S.Ctx{w, h, n, rows, its} : S.Ctx}
      loop_none.pick2(ctx, c0, t, c, found, mr, be, val, mt => ihf(e, mt))
    case False{}:
      +ctx = {S.Ctx{w, h, n, rows, its} : S.Ctx}
      loop_none.found(c0, t, found, todo, part, w, h, n, rows, its, val, shP, on0, c, mr,
        loop_found_none(S.search(c0, todo, part, ctx), c0, l => S.loop(t, l <> found, todo, part, ctx), e), ihn)

# When the loop names no cell, every one of its cells has a checked layout
# that mines it.
law loop_none:
  for +hs: List<&2, T.Pos>
  for +found: List<&2, T.Grid(Bool)>
  for +todo: S.Plan
  for +part: T.Grid(Maybe<&2, Bool>)
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +its: List<&2, S.Item>
  for e: {S.loop(hs, found, todo, part, S.Ctx{w, h, n, rows, its}) == None{} : Maybe<&2, T.Pos>}
  for +val: {all_valid(S.Ctx{w, h, n, rows, its}, found) == True{} : Bool}
  for +shP: {B.shaped(Maybe<&2, Bool>, w, h, part) == True{} : Bool}
  for +hon: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, hs) == True{} : Bool}
  for +c: T.Pos
  for m: {B.contains(hs, c) == True{} : Bool}
  Witness(S.Ctx{w, h, n, rows, its}, c)

def loop_none(hs, found, todo, part, w, h, n, rows, its, e, val, shP, hon, c, m):
  match hs:
    case Nil{}:
      Empty.absurd(Witness(S.Ctx{w, h, n, rows, its}, c), P.false_ne_true(m))
    case +c0 <> +t:
      +ht = PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, c0, t, hon)
      loop_none.cov(c0, t, found, todo, part, w, h, n, rows, its, val, shP,
        PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, c0, t, hon), c, or_cases(B.same(c0, c), B.contains(t, c), m),
        S.covered(found, c0), {==}, e,
        ef => mt => loop_none(t, found, todo, part, w, h, n, rows, its, ef, val, shP, ht, c, mt),
        l => el => vl => mt => loop_none(t, l <> found, todo, part, w, h, n, rows, its, el, vl, shP, ht, c, mt))

# The solver theorems
# ===================

law s_hidden_eq:
  for +s: T.Seen
  {S.is_hidden(s) == L.is_hidden(s) : Bool}

def s_hidden_eq(s):
  match s:
    case T.Hidden{}:
      {==}
    case T.Shown{k}:
      {==}
    case T.Boom{}:
      {==}

# Hidden in LAWS.bend's sense: on the board, and hidden in the rows.
law hid_to:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +p: T.Pos
  for +on: {B.on_board(w, h, p) == True{} : Bool}
  for +hp: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)) == True{} : Bool}
  {L.hidden(T.Knowledge{w, h, n, rows}, p) == True{} : Bool}

def hid_to(w, h, n, rows, p, on, hp):
  %Equal.sym(Bool, L.on_board(w, h, p), True{}, %PC.on_board_eq(w, h, p) : {_ == True{} : Bool}; on) :
    {Bool.and(_, L.is_hidden(L.at(T.Seen, T.Hidden{}, rows, p))) == True{} : Bool}
  %PC.at_eq(T.Seen, T.Hidden{}, rows, p) : {Bool.and(True{}, L.is_hidden(_)) == True{} : Bool}
  %s_hidden_eq(B.at(T.Seen, T.Hidden{}, rows, p)) : {Bool.and(True{}, _) == True{} : Bool}
  hp

law hid_on:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +p: T.Pos
  for hid: {L.hidden(T.Knowledge{w, h, n, rows}, p) == True{} : Bool}
  {B.on_board(w, h, p) == True{} : Bool}

def hid_on(w, h, n, rows, p, hid):
  %Equal.sym(Bool, B.on_board(w, h, p), L.on_board(w, h, p), PC.on_board_eq(w, h, p)) : {_ == True{} : Bool}
  P.and_true_l(L.on_board(w, h, p), L.is_hidden(L.at(T.Seen, T.Hidden{}, rows, p)), hid)

law hid_hp:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +p: T.Pos
  for hid: {L.hidden(T.Knowledge{w, h, n, rows}, p) == True{} : Bool}
  {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)) == True{} : Bool}

def hid_hp(w, h, n, rows, p, hid):
  %Equal.sym(Bool, S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)), L.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)),
    s_hidden_eq(B.at(T.Seen, T.Hidden{}, rows, p))) : {_ == True{} : Bool}
  %Equal.sym(T.Seen, B.at(T.Seen, T.Hidden{}, rows, p), L.at(T.Seen, T.Hidden{}, rows, p), PC.at_eq(T.Seen, T.Hidden{}, rows, p)) :
    {L.is_hidden(_) == True{} : Bool}
  P.and_true_r(L.on_board(w, h, p), L.is_hidden(L.at(T.Seen, T.Hidden{}, rows, p)), hid)

def hc_on.cell(+rows: T.Grid(T.Seen), +w: Nat, +h: Nat, +p: T.Pos, +t: List<&2, T.Pos>, +b: Bool,
  on: {B.on_board(w, h, p) == True{} : Bool},
  ih: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, S.hidden_cells(rows, t)) == True{} : Bool}) ->
  {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, List.filter.put(T.Pos, p, S.hidden_cells(rows, t), b)) == True{} : Bool}:
  match b:
    case False{}:
      ih
    case True{}:
      %Equal.sym(Bool, B.on_board(w, h, p), True{}, on) :
        {Bool.and(_, PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, S.hidden_cells(rows, t))) == True{} : Bool}
      ih

law hc_on:
  for +rows: T.Grid(T.Seen)
  for +w: Nat
  for +h: Nat
  for +ps: List<&2, T.Pos>
  for +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}
  {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, S.hidden_cells(rows, ps)) == True{} : Bool}

def hc_on(rows, w, h, ps, ons):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      hc_on.cell(rows, w, h, p, t, S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)),
        PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, p, t, ons),
        hc_on(rows, w, h, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, p, t, ons)))

law head_some:
  for +hs: List<&2, T.Pos>
  for +c: T.Pos
  for e: {List.head(&2, T.Pos, hs) == Some{c} : Maybe<&2, T.Pos>}
  {B.contains(hs, c) == True{} : Bool}

def head_some(hs, c, e):
  match hs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, PL.none_ne_some(T.Pos, c, e))
    case x <> t:
      %PL.some_inj(T.Pos, x, c, e) : {Bool.or(B.same(x, _), B.contains(t, _)) == True{} : Bool}
      or_l(B.same(x, x), B.contains(t, x), PG.same_refl(x))

law head_none:
  for +hs: List<&2, T.Pos>
  for +p: T.Pos
  for e: {List.head(&2, T.Pos, hs) == None{} : Maybe<&2, T.Pos>}
  for m: {B.contains(hs, p) == True{} : Bool}
  Empty

def head_none(hs, p, e, m):
  match hs:
    case Nil{}:
      P.false_ne_true(m)
    case x <> t:
      some_ne_none(T.Pos, x, e)

def solver_tok(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +layout: T.Grid(Bool),
  chk: {S.check(S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}, layout) == True{} : Bool}) ->
  {todos_ok(S.order(S.todos(S.items(w, h, rows, B.cells(w, h)), S.hidden_cells(rows, B.cells(w, h)))), layout) == True{} : Bool}:
  +its = S.items(w, h, rows, B.cells(w, h))
  +t0 = S.todos(its, S.hidden_cells(rows, B.cells(w, h)))
  +a = Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n))
  +iok = P.and_true_r(a, S.items_ok(its, layout), chk)
  +ta = todos_ok_all(its, S.hidden_cells(rows, B.cells(w, h)), layout, iok)
  tok_append(S.nears(t0), S.fars(t0), layout, tok_order(t0, layout, ta), tok_order_f(t0, layout, ta))

def solver_ton(+w: Nat, +h: Nat, +rows: T.Grid(T.Seen)) ->
  {todos_onb(PS.WH{w, h}, S.order(S.todos(S.items(w, h, rows, B.cells(w, h)), S.hidden_cells(rows, B.cells(w, h))))) == True{} : Bool}:
  +its = S.items(w, h, rows, B.cells(w, h))
  +t0 = S.todos(its, S.hidden_cells(rows, B.cells(w, h)))
  +ta = todos_onb_all(PS.WH{w, h}, its, S.hidden_cells(rows, B.cells(w, h)), items_onb_all(w, h, rows, B.cells(w, h), PS.cells_on(w, h)))
  ton_append(PS.WH{w, h}, S.nears(t0), S.fars(t0), ton_order(PS.WH{w, h}, t0, ta), ton_order_f(PS.WH{w, h}, t0, ta))

# The order of a search
# ======================
# Each search walks the cells in a heuristic order, then in the plain one;
# whatever the heuristic, every cell is still in the walk, and every todo in
# it is one of the solve's own.

def tok_f(l: T.Grid(Bool), t: S.Todo) -> Bool:
  match t:
    case S.Todo{c, rel}:
      S.items_ok(rel, l)

def ton_f(e: PS.WH, t: S.Todo) -> Bool:
  match t:
    case S.Todo{c, rel}:
      items_onb(e, rel)

law tok_tall:
  for +ts: List<&2, S.Todo>
  for +layout: T.Grid(Bool)
  {todos_ok(ts, layout) == PF.tall(~T.Grid(Bool), ~tok_f, layout, ts) : Bool}

def tok_tall(ts, layout):
  match ts:
    case Nil{}:
      {==}
    case S.Todo{c, rel} <> t:
      %tok_tall(t, layout) : {Bool.and(S.items_ok(rel, layout), todos_ok(t, layout))
        == Bool.and(S.items_ok(rel, layout), _) : Bool}
      {==}

law ton_tall:
  for +e: PS.WH
  for +ts: List<&2, S.Todo>
  {todos_onb(e, ts) == PF.tall(~PS.WH, ~ton_f, e, ts) : Bool}

def ton_tall(e, ts):
  match ts:
    case Nil{}:
      {==}
    case S.Todo{c, rel} <> t:
      %ton_tall(e, t) : {Bool.and(items_onb(e, rel), todos_onb(e, t)) == Bool.and(items_onb(e, rel), _) : Bool}
      {==}

law tcontains_pre:
  for +pre: List<&2, S.Todo>
  for +base: List<&2, S.Todo>
  for +q: T.Pos
  for e: {tcontains(base, q) == True{} : Bool}
  {tcontains(List.append(&2, S.Todo, pre, base), q) == True{} : Bool}

def tcontains_pre(pre, base, q, e):
  match pre:
    case Nil{}:
      e
    case S.Todo{c, rel} <> t:
      %Equal.sym(Bool, tcontains(List.append(&2, S.Todo, t, base), q), True{}, tcontains_pre(t, base, q, e)) :
        {Bool.or(B.same(c, q), _) == True{} : Bool}
      PS.or_true_r(B.same(c, q))

def or_mono(+a: Bool, +b: Bool, +b2: Bool, k: {b == True{} : Bool} -> {b2 == True{} : Bool},
  e: {Bool.or(a, b) == True{} : Bool}) -> {Bool.or(a, b2) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      k(e)

# Cells still to do stay to do with more todos in front.
law covers_pre:
  for +pre: List<&2, S.Todo>
  for +base: List<&2, S.Todo>
  for +part: T.Grid(Maybe<&2, Bool>)
  for +ps: List<&2, T.Pos>
  for +cv: {PS.allp(~CV, ~cv_f, CV{base, part}, ps) == True{} : Bool}
  {PS.allp(~CV, ~cv_f, CV{List.append(&2, S.Todo, pre, base), part}, ps) == True{} : Bool}

def covers_pre(pre, base, part, ps, cv):
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +a = Bool.not(S.is_none(S.look(part, q)))
      +app = List.append(&2, S.Todo, pre, base)
      +hd = or_mono(a, tcontains(base, q), tcontains(app, q), m => tcontains_pre(pre, base, q, m),
        PS.allp_head(~CV, ~cv_f, CV{base, part}, q, t, cv))
      %Equal.sym(Bool, PS.allp(~CV, ~cv_f, CV{app, part}, t), True{},
        covers_pre(pre, base, part, t, PS.allp_tail(~CV, ~cv_f, CV{base, part}, q, t, cv))) :
        {Bool.and(cv_f(CV{app, part}, q), _) == True{} : Bool}
      %Equal.sym(Bool, cv_f(CV{app, part}, q), True{}, hd) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

# The heuristic order of the search for c, as the plan builds it.
def plan_qs(+c: T.Pos, +w: Nat, +h: Nat, +ts: List<&2, S.Todo>) -> List<&2, T.Pos>:
  +near = S.nears(ts)
  +fuel = Nat.add(List.length(&2, S.Todo, near), 1n)
  +relg = S.rel_grid(w, h, near)
  List.append(&2, T.Pos, S.linked(c, w, h, fuel, relg), S.groups(w, h, near, fuel, relg))

def plan_k(+c: T.Pos, +w: Nat, +n: Nat, +ts: List<&2, S.Todo>) -> Nat:
  S.spin(c, w, n, List.length(&2, S.Todo, S.fars(ts)))

def plan_list(+c: T.Pos, +w: Nat, +h: Nat, +n: Nat, +ts: List<&2, S.Todo>) -> List<&2, S.Todo>:
  List.append(&2, S.Todo, S.gather(plan_qs(c, w, h, ts), S.nears(ts)),
    List.append(&2, S.Todo, S.rot(S.fars(ts), plan_k(c, w, n, ts)), S.order(ts)))

law plan_shape:
  for +c: T.Pos
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +its: List<&2, S.Item>
  for +ts: List<&2, S.Todo>
  {S.plan_todo(c, S.plan(w, h, ts), S.Ctx{w, h, n, rows, its}) == plan_list(c, w, h, n, ts) : List<&2, S.Todo>}

def plan_shape(c, w, h, n, rows, its, ts):
  {==}

# A failed search for c rules out every consistent layout mining c.
law search_none:
  for +w: Nat
  for +h: Nat
  for +n: Nat
  for +rows: T.Grid(T.Seen)
  for +okt: {B.shaped(T.Seen, w, h, rows) == True{} : Bool}
  for +c: T.Pos
  for +onc: {B.on_board(w, h, c) == True{} : Bool}
  for +layout: T.Grid(Bool)
  for +cons: {L.consistent(T.Knowledge{w, h, n, rows}, layout) == True{} : Bool}
  for +mc: {B.mine(layout, c) == True{} : Bool}
  for sn: {S.search(c, S.plan(w, h, S.todos(S.items(w, h, rows, B.cells(w, h)), S.hidden_cells(rows, B.cells(w, h)))),
    S.start(rows), S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}) == None{} : Maybe<&2, T.Grid(Bool)>}
  Empty

def search_none(w, h, n, rows, okt, c, onc, layout, cons, mc, sn):
  +its = S.items(w, h, rows, B.cells(w, h))
  +hs = S.hidden_cells(rows, B.cells(w, h))
  +t0 = S.todos(its, hs)
  +ctx = {S.Ctx{w, h, n, rows, its} : S.Ctx}
  +shS = Equal.trans(Bool, B.shaped(Maybe<&2, Bool>, w, h, S.start(rows)), B.shaped(T.Seen, w, h, rows), True{},
    start_shaped(w, h, rows), okt)
  +chk = Equal.trans(Bool, S.check(S.Ctx{w, h, n, rows, its}, layout), L.consistent(T.Knowledge{w, h, n, rows}, layout), True{},
    check_cons(w, h, n, rows, layout), cons)
  +shL = {%Equal.sym(Bool, B.shaped(Bool, w, h, layout), L.shaped(Bool, w, h, layout), PC.shaped_eq(Bool, w, h, layout)) :
      {_ == True{} : Bool};
    PW.and4_a(L.shaped(Bool, w, h, layout), L.shaped(T.Seen, w, h, rows), Nat.is_eq(L.total_mines(layout), n),
      L.agrees_all(w, h, rows, layout, L.cells(w, h)), cons) : {B.shaped(Bool, w, h, layout) == True{} : Bool}}
  +p = B.set_at(Maybe<&2, Bool>, S.start(rows), c, Some{True{}})
  +shp = PL.shaped_set(Maybe<&2, Bool>, w, h, S.start(rows), c, Some{True{}}, shS)
  +qs = plan_qs(c, w, h, t0)
  +k = plan_k(c, w, n, t0)
  +todo = plan_list(c, w, h, n, t0)
  +con = PF.tall_plan(~PS.WH, ~PF.con_f, PS.WH{w, h}, t0, qs, k,
    PF.con_todos(w, h, its, hs, hc_on(rows, w, h, B.cells(w, h), PS.cells_on(w, h))))
  +eq = PF.dfs2_eq(todo, p, w, h, n, rows, its, S.part_true(p), S.part_none(p), shp, con, {==}, {==})
  +sn1 = {%Equal.sym(List<&2, S.Todo>, S.plan_todo(c, S.plan(w, h, t0), ctx), todo, plan_shape(c, w, h, n, rows, its, t0)) :
      {S.dfs2(_, p, S.part_true(p), S.part_none(p), ctx) == None{} : Maybe<&2, T.Grid(Bool)>};
    sn : {S.dfs2(todo, p, S.part_true(p), S.part_none(p), ctx) == None{} : Maybe<&2, T.Grid(Bool)>}}
  +sn2 = Equal.trans(Maybe<&2, T.Grid(Bool)>, S.dfs(todo, p, ctx), S.dfs2(todo, p, S.part_true(p), S.part_none(p), ctx), None{},
    Equal.sym(Maybe<&2, T.Grid(Bool)>, S.dfs2(todo, p, S.part_true(p), S.part_none(p), ctx), S.dfs(todo, p, ctx), eq), sn1)
  +rest = List.append(&2, S.Todo, S.rot(S.fars(t0), k), S.order(t0))
  +cov = covers_pre(S.gather(qs, S.nears(t0)), rest, p, B.cells(w, h),
    covers_pre(S.rot(S.fars(t0), k), S.order(t0), p, B.cells(w, h),
      start_cover.go(w, h, rows, its, c, shS, B.cells(w, h), PS.cells_on(w, h))))
  +a = Bool.and(Bool.and(B.shaped(Bool, w, h, layout), B.shaped(T.Seen, w, h, rows)), Nat.is_eq(B.total_mines(layout), n))
  +ta = todos_ok_all(its, hs, layout, P.and_true_r(a, S.items_ok(its, layout), chk))
  +tok = {%Equal.sym(Bool, todos_ok(todo, layout), PF.tall(~T.Grid(Bool), ~tok_f, layout, todo), tok_tall(todo, layout)) :
      {_ == True{} : Bool};
    PF.tall_plan(~T.Grid(Bool), ~tok_f, layout, t0, qs, k,
      Equal.trans(Bool, PF.tall(~T.Grid(Bool), ~tok_f, layout, t0), todos_ok(t0, layout), True{},
        Equal.sym(Bool, todos_ok(t0, layout), PF.tall(~T.Grid(Bool), ~tok_f, layout, t0), tok_tall(t0, layout)), ta)) :
      {todos_ok(todo, layout) == True{} : Bool}}
  +e = {PS.WH{w, h} : PS.WH}
  +tn = todos_onb_all(e, its, hs, items_onb_all(w, h, rows, B.cells(w, h), PS.cells_on(w, h)))
  +ton = {%Equal.sym(Bool, todos_onb(e, todo), PF.tall(~PS.WH, ~ton_f, e, todo), ton_tall(e, todo)) :
      {_ == True{} : Bool};
    PF.tall_plan(~PS.WH, ~ton_f, e, t0, qs, k,
      Equal.trans(Bool, PF.tall(~PS.WH, ~ton_f, e, t0), todos_onb(e, t0), True{},
        Equal.sym(Bool, todos_onb(e, t0), PF.tall(~PS.WH, ~ton_f, e, t0), ton_tall(e, t0)), tn)) :
      {todos_onb(e, todo) == True{} : Bool}}
  dfs_none(todo, p, w, h, n, rows, its, layout, sn2, shp, shL, cov,
    comp_set(w, h, c, S.start(rows), layout, True{}, shS, mc, B.cells(w, h), PS.cells_on(w, h),
      start_comp(w, h, n, rows, layout, cons)),
    chk, tok, ton, items_onb_all(w, h, rows, B.cells(w, h), PS.cells_on(w, h)))

def safe_fn(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +okt: {B.shaped(T.Seen, w, h, rows) == True{} : Bool},
  +c: T.Pos, +onc: {B.on_board(w, h, c) == True{} : Bool},
  +sn: {S.search(c, S.plan(w, h, S.todos(S.items(w, h, rows, B.cells(w, h)), S.hidden_cells(rows, B.cells(w, h)))),
    S.start(rows), S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}) == None{} : Maybe<&2, T.Grid(Bool)>},
  +layout: T.Grid(Bool), +cons: {L.consistent(T.Knowledge{w, h, n, rows}, layout) == True{} : Bool},
  +b: Bool, be: {B.mine(layout, c) == b : Bool}) -> {L.mine(layout, c) == False{} : Bool}:
  match b:
    case False{}:
      %PC.mine_eq(layout, c) : {_ == False{} : Bool}
      be
    case True{}:
      Empty.absurd({L.mine(layout, c) == False{} : Bool}, search_none(w, h, n, rows, okt, c, onc, layout, cons, be, sn))

def PF_both(+a: Bool, e1: {a == False{} : Bool}, e2: {a == True{} : Bool}, -A: Type) -> A:
  Empty.absurd(A, P.false_ne_true(Equal.trans(Bool, False{}, a, True{}, Equal.sym(Bool, a, False{}, e1), e2)))

def safe_none(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), okf: {B.shaped(T.Seen, w, h, rows) == False{} : Bool},
  +c: T.Pos, +layout: T.Grid(Bool), cons: {L.consistent(T.Knowledge{w, h, n, rows}, layout) == True{} : Bool}) ->
  {L.mine(layout, c) == False{} : Bool}:
  PF_both(B.shaped(T.Seen, w, h, rows), okf,
    %Equal.sym(Bool, B.shaped(T.Seen, w, h, rows), L.shaped(T.Seen, w, h, rows), PC.shaped_eq(T.Seen, w, h, rows)) :
      {_ == True{} : Bool};
    PW.and4_b(L.shaped(Bool, w, h, layout), L.shaped(T.Seen, w, h, rows), Nat.is_eq(L.total_mines(layout), n),
      L.agrees_all(w, h, rows, layout, L.cells(w, h)), cons), {L.mine(layout, c) == False{} : Bool})

def safe_hidden(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +c: T.Pos,
  hc: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, c)) == True{} : Bool} & {B.contains(B.cells(w, h), c) == True{} : Bool},
  fn: @layout: T.Grid(Bool) -> {L.consistent(T.Knowledge{w, h, n, rows}, layout) == True{} : Bool} -> {L.mine(layout, c) == False{} : Bool}) ->
  L.ProvablySafe(T.Knowledge{w, h, n, rows}, c):
  match hc:
    case (hp, mc):
      (hid_to(w, h, n, rows, c, PS.allp_member(~PS.WH, ~PS.onb, PS.WH{w, h}, B.cells(w, h), c, PS.cells_on(w, h), mc), hp), fn)

def safe_hidden.k(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +c: T.Pos,
  hc: {S.is_hidden(B.at(T.Seen, T.Hidden{}, rows, c)) == True{} : Bool} & {B.contains(B.cells(w, h), c) == True{} : Bool},
  fn: {B.on_board(w, h, c) == True{} : Bool} ->
    @layout: T.Grid(Bool) -> {L.consistent(T.Knowledge{w, h, n, rows}, layout) == True{} : Bool} -> {L.mine(layout, c) == False{} : Bool}) ->
  L.ProvablySafe(T.Knowledge{w, h, n, rows}, c):
  match hc:
    case (hp, mc):
      +onc = PS.allp_member(~PS.WH, ~PS.onb, PS.WH{w, h}, B.cells(w, h), c, PS.cells_on(w, h), mc)
      (hid_to(w, h, n, rows, c, onc, hp), fn(onc))

def solve_safe.k(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +c: T.Pos,
  +okt: {B.shaped(T.Seen, w, h, rows) == True{} : Bool},
  ls: LoopSome(S.hidden_cells(rows, B.cells(w, h)), S.plan(w, h, S.todos(S.items(w, h, rows, B.cells(w, h)), S.hidden_cells(rows, B.cells(w, h)))),
    S.start(rows), S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}, c)) ->
  L.ProvablySafe(T.Knowledge{w, h, n, rows}, c):
  match ls:
    case (m, sn):
      hc = hc_sound(rows, B.cells(w, h), c, m)
      safe_hidden.k(w, h, n, rows, c, hc, onc => +layout => cons => safe_fn(w, h, n, rows, okt, c, onc, sn, layout, cons, B.mine(layout, c), {==}))

def solve_safe.go(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +c: T.Pos, +ok: Bool,
  oke: {B.shaped(T.Seen, w, h, rows) == ok : Bool},
  e: {S.solve.go(ok, S.hidden_cells(rows, B.cells(w, h)), w, h, n, rows) == Some{c} : Maybe<&2, T.Pos>}) ->
  L.ProvablySafe(T.Knowledge{w, h, n, rows}, c):
  match ok:
    case False{}:
      +hs = S.hidden_cells(rows, B.cells(w, h))
      safe_hidden(w, h, n, rows, c, hc_sound(rows, B.cells(w, h), c, head_some(hs, c, e)),
        layout => cons => safe_none(w, h, n, rows, oke, c, layout, cons))
    case True{}:
      +hs = S.hidden_cells(rows, B.cells(w, h))
      +its = S.items(w, h, rows, B.cells(w, h))
      ls = loop_some(hs, Nil{}, S.plan(w, h, S.todos(its, hs)), S.start(rows), S.Ctx{w, h, n, rows, its}, c, e)
      solve_safe.k(w, h, n, rows, c, oke, ls)

# Witness soundness: a cell the solver names is provably safe.
law solve_safe:
  for +k: T.Knowledge
  for +c: T.Pos
  for e: {S.solve(k) == Some{c} : Maybe<&2, T.Pos>}
  L.ProvablySafe(k, c)

def solve_safe(k, c, e):
  match k:
    case T.Knowledge{w, h, n, rows}:
      solve_safe.go(w, h, n, rows, c, B.shaped(T.Seen, w, h, rows), {==}, e)

def stuck_wit(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +p: T.Pos,
  H: @layout: T.Grid(Bool) -> {L.consistent(T.Knowledge{w, h, n, rows}, layout) == True{} : Bool} -> {L.mine(layout, p) == False{} : Bool},
  wt: Witness(S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}, p)) -> Empty:
  match wt:
    case (+l, pr):
      match pr:
        case (chk, ml):
          PF_both(L.mine(l, p),
            H(l, Equal.trans(Bool, L.consistent(T.Knowledge{w, h, n, rows}, l),
              S.check(S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}, l), True{},
              Equal.sym(Bool, S.check(S.Ctx{w, h, n, rows, S.items(w, h, rows, B.cells(w, h))}, l),
                L.consistent(T.Knowledge{w, h, n, rows}, l), check_cons(w, h, n, rows, l)), chk)),
            %PC.mine_eq(l, p) : {_ == True{} : Bool}; ml, Empty)

def solve_stuck.go(+w: Nat, +h: Nat, +n: Nat, +rows: T.Grid(T.Seen), +ok: Bool,
  oke: {B.shaped(T.Seen, w, h, rows) == ok : Bool},
  e: {S.solve.go(ok, S.hidden_cells(rows, B.cells(w, h)), w, h, n, rows) == None{} : Maybe<&2, T.Pos>},
  +p: T.Pos, ps: L.ProvablySafe(T.Knowledge{w, h, n, rows}, p)) -> Empty:
  match ok:
    case False{}:
      match ps:
        case (+hid, H):
          head_none(S.hidden_cells(rows, B.cells(w, h)), p, e,
            hc_member(rows, B.cells(w, h), p, PS.cells_member(w, h, p, hid_on(w, h, n, rows, p, hid)), hid_hp(w, h, n, rows, p, hid)))
    case True{}:
      match ps:
        case (+hid, H):
          +hs = S.hidden_cells(rows, B.cells(w, h))
          +its = S.items(w, h, rows, B.cells(w, h))
          +shS = Equal.trans(Bool, B.shaped(Maybe<&2, Bool>, w, h, S.start(rows)), B.shaped(T.Seen, w, h, rows), True{},
            start_shaped(w, h, rows), oke)
          +mp = hc_member(rows, B.cells(w, h), p, PS.cells_member(w, h, p, hid_on(w, h, n, rows, p, hid)), hid_hp(w, h, n, rows, p, hid))
          stuck_wit(w, h, n, rows, p, H,
            loop_none(hs, Nil{}, S.plan(w, h, S.todos(its, hs)), S.start(rows), w, h, n, rows, its, e, {==}, shS,
              hc_on(rows, w, h, B.cells(w, h), PS.cells_on(w, h)), p, mp))

def solve_stuck.k(+k: T.Knowledge, e: {S.solve(k) == None{} : Maybe<&2, T.Pos>}, +p: T.Pos, ps: L.ProvablySafe(k, p)) -> Empty:
  match k:
    case T.Knowledge{w, h, n, rows}:
      solve_stuck.go(w, h, n, rows, B.shaped(T.Seen, w, h, rows), {==}, e, p, ps)

# Stuck soundness: when the solver names no cell, no cell is provably safe.
law solve_stuck:
  for +k: T.Knowledge
  for e: {S.solve(k) == None{} : Maybe<&2, T.Pos>}
  L.Stuck(k)

def solve_stuck(k, e):
  p => ps => solve_stuck.k(k, e, p, ps)
