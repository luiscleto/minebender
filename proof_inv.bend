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
import ./proof_flood.bend as PF
import ./solver.bend as S

# The invariant of real games, and that every action keeps it.

# Closure: every revealed zero has its neighbours revealed
# ========================================================

def shown_in(g: T.Grid(Bool), q: T.Pos) -> Bool:
  B.at(Bool, False{}, g, q)

type CL is Data:
  CL{w: Nat, h: Nat, layout: T.Grid(Bool), g: T.Grid(Bool)}

def cl_f.go(e: CL, +q: T.Pos) -> Bool:
  match e:
    case CL{+w, +h, layout, +g}:
      Bool.not(B.at(Bool, False{}, g, q) && B.zero(w, h, layout, q))
        || PS.allp(~T.Grid(Bool), ~shown_in, g, B.neighbours(w, h, q))

def cl_f(e: CL, q: T.Pos) -> Bool:
  cl_f.go(e, q)

def closed(+w: Nat, +h: Nat, layout: T.Grid(Bool), g: T.Grid(Bool)) -> Bool:
  PS.allp(~CL, ~cl_f, CL{w, h, layout, g}, B.cells(w, h))

def closed_use.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: T.Grid(Bool), +q: T.Pos, +r: T.Pos,
  f: {Bool.or(Bool.not(Bool.and(True{}, True{})),
    PS.allp(~T.Grid(Bool), ~shown_in, g, B.neighbours(w, h, q))) == True{} : Bool},
  rm: {B.contains(B.neighbours(w, h, q), r) == True{} : Bool}) ->
  {B.at(Bool, False{}, g, r) == True{} : Bool}:
  PS.allp_member(~T.Grid(Bool), ~shown_in, g, B.neighbours(w, h, q), r, f, rm)

# In a closed grid, a revealed zero's neighbours are revealed.
law closed_use:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: T.Grid(Bool)
  for c: {closed(w, h, layout, g) == True{} : Bool}
  for +q: T.Pos
  for on: {B.on_board(w, h, q) == True{} : Bool}
  for gq: {B.at(Bool, False{}, g, q) == True{} : Bool}
  for z: {B.zero(w, h, layout, q) == True{} : Bool}
  for +r: T.Pos
  for rm: {B.contains(B.neighbours(w, h, q), r) == True{} : Bool}
  {B.at(Bool, False{}, g, r) == True{} : Bool}

def closed_use(w, h, layout, g, c, q, on, gq, z, r, rm):
  +f = PS.allp_member(~CL, ~cl_f, CL{w, h, layout, g}, B.cells(w, h), q, c, PS.cells_member(w, h, q, on))
  closed_use.go(w, h, layout, g, q, r,
    %gq : {Bool.or(Bool.not(Bool.and(_, True{})),
        PS.allp(~T.Grid(Bool), ~shown_in, g, B.neighbours(w, h, q))) == True{} : Bool};
    %z : {Bool.or(Bool.not(Bool.and(B.at(Bool, False{}, g, q), _)),
        PS.allp(~T.Grid(Bool), ~shown_in, g, B.neighbours(w, h, q))) == True{} : Bool};
    f, rm)

# After a flood
# =============

# The flood's one-cell closure fact: a revealed zero's neighbour is revealed.
def flood_fact.go(+n: Nat, +work: List<&2, G.Work>, +hd: Bool, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +cnt: {n == B.count_false(shown) : Nat},
  +he: {G.head_hidden(w, h, shown, work) == hd : Bool}, +q: T.Pos, on: {B.on_board(w, h, q) == True{} : Bool},
  after: {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q) == True{} : Bool},
  +z: {B.zero(w, h, layout, q) == True{} : Bool}, +r: T.Pos,
  +rm: {B.contains(B.neighbours(w, h, q), r) == True{} : Bool},
  +s: Bool, se: {B.at(Bool, False{}, shown, q) == s : Bool}) ->
  {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), r) == True{} : Bool}:
  match s:
    case True{}:
      PF.flood_mono(n, work, hd, w, h, layout, shown, r, closed_use(w, h, layout, shown, cl, q, on, se, z, r, rm))
    case False{}:
      PF.flood_zero(n, work, hd, w, h, layout, shown, sh, cnt, he, q, se, after, z, r, rm)

def closed_flood.nbrs(+n: Nat, +work: List<&2, G.Work>, +hd: Bool, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +cnt: {n == B.count_false(shown) : Nat},
  +he: {G.head_hidden(w, h, shown, work) == hd : Bool}, +q: T.Pos, +on: {B.on_board(w, h, q) == True{} : Bool},
  +after: {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q) == True{} : Bool},
  +z: {B.zero(w, h, layout, q) == True{} : Bool}, ns: List<&2, T.Pos>,
  +adj: {PS.allp(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, q}, ns) == True{} : Bool}) ->
  {PS.allp(~T.Grid(Bool), ~shown_in, G.flood(n, work, hd, w, h, layout, shown), ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +r <> +t:
      +ar = PS.allp_head(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, q}, r, t, adj)
      +rm = PS.neighbours_member(w, h, q, r, P.and_true_r(B.adjacent(q, r), B.on_board(w, h, r), ar),
        P.and_true_l(B.adjacent(q, r), B.on_board(w, h, r), ar))
      +F = G.flood(n, work, hd, w, h, layout, shown)
      %Equal.sym(Bool, B.at(Bool, False{}, F, r), True{},
        flood_fact.go(n, work, hd, w, h, layout, shown, sh, cl, cnt, he, q, on, after, z, r, rm,
          B.at(Bool, False{}, shown, q), {==})) :
        {Bool.and(_, PS.allp(~T.Grid(Bool), ~shown_in, F, t)) == True{} : Bool}
      closed_flood.nbrs(n, work, hd, w, h, layout, shown, sh, cl, cnt, he, q, on, after, z, t,
        PS.allp_tail(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, q}, r, t, adj))

def closed_flood.cell(+n: Nat, +work: List<&2, G.Work>, +hd: Bool, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +cnt: {n == B.count_false(shown) : Nat},
  +he: {G.head_hidden(w, h, shown, work) == hd : Bool}, +q: T.Pos, +on: {B.on_board(w, h, q) == True{} : Bool},
  +b: Bool, +be: {Bool.and(B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q), B.zero(w, h, layout, q)) == b : Bool}) ->
  {cl_f(CL{w, h, layout, G.flood(n, work, hd, w, h, layout, shown)}, q) == True{} : Bool}:
  match b:
    case False{}:
      +F = G.flood(n, work, hd, w, h, layout, shown)
      %Equal.sym(Bool, Bool.and(B.at(Bool, False{}, F, q), B.zero(w, h, layout, q)), False{}, be) :
        {Bool.or(Bool.not(_), PS.allp(~T.Grid(Bool), ~shown_in, F, B.neighbours(w, h, q))) == True{} : Bool}
      {==}
    case True{}:
      +F = G.flood(n, work, hd, w, h, layout, shown)
      +fq = P.and_true_l(B.at(Bool, False{}, F, q), B.zero(w, h, layout, q), be)
      +zq = P.and_true_r(B.at(Bool, False{}, F, q), B.zero(w, h, layout, q), be)
      %Equal.sym(Bool, Bool.and(B.at(Bool, False{}, F, q), B.zero(w, h, layout, q)), True{}, be) :
        {Bool.or(Bool.not(_), PS.allp(~T.Grid(Bool), ~shown_in, F, B.neighbours(w, h, q))) == True{} : Bool}
      closed_flood.nbrs(n, work, hd, w, h, layout, shown, sh, cl, cnt, he, q, on, fq, zq,
        B.neighbours(w, h, q), PS.neighbours_all(w, h, q))

def closed_flood.cells(+n: Nat, +work: List<&2, G.Work>, +hd: Bool, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +cnt: {n == B.count_false(shown) : Nat},
  +he: {G.head_hidden(w, h, shown, work) == hd : Bool}, ps: List<&2, T.Pos>,
  +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}) ->
  {PS.allp(~CL, ~cl_f, CL{w, h, layout, G.flood(n, work, hd, w, h, layout, shown)}, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +F = G.flood(n, work, hd, w, h, layout, shown)
      %Equal.sym(Bool, cl_f(CL{w, h, layout, F}, q), True{},
        closed_flood.cell(n, work, hd, w, h, layout, shown, sh, cl, cnt, he, q,
          PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons),
          Bool.and(B.at(Bool, False{}, F, q), B.zero(w, h, layout, q)), {==})) :
        {Bool.and(_, PS.allp(~CL, ~cl_f, CL{w, h, layout, F}, t)) == True{} : Bool}
      closed_flood.cells(n, work, hd, w, h, layout, shown, sh, cl, cnt, he, t,
        PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))

# A flood from a closed grid leaves a closed grid.
law closed_flood:
  for +n: Nat
  for +work: List<&2, G.Work>
  for +hd: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  for +cl: {closed(w, h, layout, shown) == True{} : Bool}
  for +cnt: {n == B.count_false(shown) : Nat}
  for +he: {G.head_hidden(w, h, shown, work) == hd : Bool}
  {closed(w, h, layout, G.flood(n, work, hd, w, h, layout, shown)) == True{} : Bool}

def closed_flood(n, work, hd, w, h, layout, shown, sh, cl, cnt, he):
  closed_flood.cells(n, work, hd, w, h, layout, shown, sh, cl, cnt, he, B.cells(w, h), PS.cells_on(w, h))

# After an explosion
# ==================

def zero_not_mine(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +q: T.Pos,
  z: {B.zero(w, h, layout, q) == True{} : Bool}) -> {B.mine(layout, q) == False{} : Bool}:
  +a = Bool.and(B.on_board(w, h, q), Bool.not(B.mine(layout, q)))
  P.not_true(B.mine(layout, q),
    P.and_true_r(B.on_board(w, h, q), Bool.not(B.mine(layout, q)),
      P.and_true_l(a, Nat.is_eq(B.adj_mines(w, h, layout, q), 0n), z)))

def explode_fact.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +p: T.Pos,
  mp: {B.mine(layout, p) == True{} : Bool}, +cl: {closed(w, h, layout, shown) == True{} : Bool},
  +q: T.Pos, on: {B.on_board(w, h, q) == True{} : Bool},
  after: {B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), q) == True{} : Bool},
  +z: {B.zero(w, h, layout, q) == True{} : Bool}, +r: T.Pos,
  +rm: {B.contains(B.neighbours(w, h, q), r) == True{} : Bool},
  +b: Bool, be: {B.same(p, q) == b : Bool}) ->
  {B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), r) == True{} : Bool}:
  match b:
    case True{}:
      PF.both_absurd({B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), r) == True{} : Bool},
        B.mine(layout, q), zero_not_mine(w, h, layout, q, z),
        %PG.same_sound(p, q, be) : {B.mine(layout, _) == True{} : Bool}; mp)
    case False{}:
      PF.at_set_mono(shown, p, r,
        closed_use(w, h, layout, shown, cl, q, on,
          %PL.at_set_ne(Bool, shown, p, q, True{}, False{}, be) : {_ == True{} : Bool}; after, z, r, rm))

def closed_explode.nbrs(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +p: T.Pos,
  +mp: {B.mine(layout, p) == True{} : Bool}, +cl: {closed(w, h, layout, shown) == True{} : Bool},
  +q: T.Pos, +on: {B.on_board(w, h, q) == True{} : Bool},
  +after: {B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), q) == True{} : Bool},
  +z: {B.zero(w, h, layout, q) == True{} : Bool}, ns: List<&2, T.Pos>,
  +adj: {PS.allp(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, q}, ns) == True{} : Bool}) ->
  {PS.allp(~T.Grid(Bool), ~shown_in, B.set_at(Bool, shown, p, True{}), ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +r <> +t:
      +ar = PS.allp_head(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, q}, r, t, adj)
      +rm = PS.neighbours_member(w, h, q, r, P.and_true_r(B.adjacent(q, r), B.on_board(w, h, r), ar),
        P.and_true_l(B.adjacent(q, r), B.on_board(w, h, r), ar))
      +s2 = B.set_at(Bool, shown, p, True{})
      %Equal.sym(Bool, B.at(Bool, False{}, s2, r), True{},
        explode_fact.go(w, h, layout, shown, p, mp, cl, q, on, after, z, r, rm, B.same(p, q), {==})) :
        {Bool.and(_, PS.allp(~T.Grid(Bool), ~shown_in, s2, t)) == True{} : Bool}
      closed_explode.nbrs(w, h, layout, shown, p, mp, cl, q, on, after, z, t,
        PS.allp_tail(~PS.WHS, ~PS.adj_on, PS.WHS{w, h, q}, r, t, adj))

def closed_explode.cell(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +p: T.Pos,
  +mp: {B.mine(layout, p) == True{} : Bool}, +cl: {closed(w, h, layout, shown) == True{} : Bool},
  +q: T.Pos, +on: {B.on_board(w, h, q) == True{} : Bool}, +b: Bool,
  +be: {Bool.and(B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), q), B.zero(w, h, layout, q)) == b : Bool}) ->
  {cl_f(CL{w, h, layout, B.set_at(Bool, shown, p, True{})}, q) == True{} : Bool}:
  match b:
    case False{}:
      +s2 = B.set_at(Bool, shown, p, True{})
      %Equal.sym(Bool, Bool.and(B.at(Bool, False{}, s2, q), B.zero(w, h, layout, q)), False{}, be) :
        {Bool.or(Bool.not(_), PS.allp(~T.Grid(Bool), ~shown_in, s2, B.neighbours(w, h, q))) == True{} : Bool}
      {==}
    case True{}:
      +s2 = B.set_at(Bool, shown, p, True{})
      %Equal.sym(Bool, Bool.and(B.at(Bool, False{}, s2, q), B.zero(w, h, layout, q)), True{}, be) :
        {Bool.or(Bool.not(_), PS.allp(~T.Grid(Bool), ~shown_in, s2, B.neighbours(w, h, q))) == True{} : Bool}
      closed_explode.nbrs(w, h, layout, shown, p, mp, cl, q, on,
        P.and_true_l(B.at(Bool, False{}, s2, q), B.zero(w, h, layout, q), be),
        P.and_true_r(B.at(Bool, False{}, s2, q), B.zero(w, h, layout, q), be),
        B.neighbours(w, h, q), PS.neighbours_all(w, h, q))

def closed_explode.cells(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +p: T.Pos,
  +mp: {B.mine(layout, p) == True{} : Bool}, +cl: {closed(w, h, layout, shown) == True{} : Bool},
  ps: List<&2, T.Pos>, +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}) ->
  {PS.allp(~CL, ~cl_f, CL{w, h, layout, B.set_at(Bool, shown, p, True{})}, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +s2 = B.set_at(Bool, shown, p, True{})
      %Equal.sym(Bool, cl_f(CL{w, h, layout, s2}, q), True{},
        closed_explode.cell(w, h, layout, shown, p, mp, cl, q,
          PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons),
          Bool.and(B.at(Bool, False{}, s2, q), B.zero(w, h, layout, q)), {==})) :
        {Bool.and(_, PS.allp(~CL, ~cl_f, CL{w, h, layout, s2}, t)) == True{} : Bool}
      closed_explode.cells(w, h, layout, shown, p, mp, cl, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))

law closed_explode:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +p: T.Pos
  for +mp: {B.mine(layout, p) == True{} : Bool}
  for +cl: {closed(w, h, layout, shown) == True{} : Bool}
  {closed(w, h, layout, B.set_at(Bool, shown, p, True{})) == True{} : Bool}

def closed_explode(w, h, layout, shown, p, mp, cl):
  closed_explode.cells(w, h, layout, shown, p, mp, cl, B.cells(w, h), PS.cells_on(w, h))

# The blank grid is closed
# ========================

def closed_blank.cell(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +q: T.Pos) ->
  {cl_f(CL{w, h, layout, B.blank(Bool, w, h, False{})}, q) == True{} : Bool}:
  match q:
    case T.Pos{x, y}:
      +bl = B.blank(Bool, w, h, False{})
      %Equal.sym(Bool, B.at(Bool, False{}, bl, T.Pos{x, y}), False{}, PL.blank_at(w, h, x, y)) :
        {Bool.or(Bool.not(Bool.and(_, B.zero(w, h, layout, T.Pos{x, y}))),
          PS.allp(~T.Grid(Bool), ~shown_in, bl, B.neighbours(w, h, T.Pos{x, y}))) == True{} : Bool}
      {==}

def closed_blank.cells(+w: Nat, +h: Nat, +layout: T.Grid(Bool), ps: List<&2, T.Pos>) ->
  {PS.allp(~CL, ~cl_f, CL{w, h, layout, B.blank(Bool, w, h, False{})}, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case q <> t:
      %Equal.sym(Bool, cl_f(CL{w, h, layout, B.blank(Bool, w, h, False{})}, q), True{},
        closed_blank.cell(w, h, layout, q)) :
        {Bool.and(_, PS.allp(~CL, ~cl_f, CL{w, h, layout, B.blank(Bool, w, h, False{})}, t)) == True{} : Bool}
      closed_blank.cells(w, h, layout, t)

law closed_blank:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  {closed(w, h, layout, B.blank(Bool, w, h, False{})) == True{} : Bool}

def closed_blank(w, h, layout):
  closed_blank.cells(w, h, layout, B.cells(w, h))

# No revealed mine
# ================

type LS is Data:
  LS{layout: T.Grid(Bool), g: T.Grid(Bool)}

def nsm_f.go(e: LS, +q: T.Pos) -> Bool:
  match e:
    case LS{layout, g}:
      Bool.not(B.at(Bool, False{}, g, q) && B.mine(layout, q))

def nsm_f(e: LS, q: T.Pos) -> Bool:
  nsm_f.go(e, q)

def nsm(w: Nat, h: Nat, layout: T.Grid(Bool), g: T.Grid(Bool)) -> Bool:
  PS.allp(~LS, ~nsm_f, LS{layout, g}, B.cells(w, h))

def nsm_use.go(+layout: T.Grid(Bool), +g: T.Grid(Bool), +q: T.Pos,
  f: {Bool.not(Bool.and(B.at(Bool, False{}, g, q), True{})) == True{} : Bool}) ->
  {B.at(Bool, False{}, g, q) == False{} : Bool}:
  P.not_true(B.at(Bool, False{}, g, q),
    %P.and_true_r_id(B.at(Bool, False{}, g, q)) : {Bool.not(_) == True{} : Bool}; f)

# Without a revealed mine, a mine of the board is not revealed.
law nsm_use:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: T.Grid(Bool)
  for n: {nsm(w, h, layout, g) == True{} : Bool}
  for +q: T.Pos
  for on: {B.on_board(w, h, q) == True{} : Bool}
  for m: {B.mine(layout, q) == True{} : Bool}
  {B.at(Bool, False{}, g, q) == False{} : Bool}

def nsm_use(w, h, layout, g, n, q, on, m):
  nsm_use.go(layout, g, q,
    %m : {Bool.not(Bool.and(B.at(Bool, False{}, g, q), _)) == True{} : Bool};
    PS.allp_member(~LS, ~nsm_f, LS{layout, g}, B.cells(w, h), q, n, PS.cells_member(w, h, q, on)))

def nsm_flood.walk(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +p0: T.Pos, +q: T.Pos,
  safe: {L.mine(layout, p0) == False{} : Bool}, mq: {B.mine(layout, q) == True{} : Bool},
  wk: PF.Walk(w, h, layout, p0, q), -A: Type) -> A:
  match wk:
    case (path, pw):
      PF.both_absurd(A, L.mine(layout, q), PW.walk_safe(path, w, h, layout, p0, q, pw, safe),
        %PC.mine_eq(layout, q) : {_ == True{} : Bool}; mq)

def nsm_flood.new(+n: Nat, +work: List<&2, G.Work>, +hd: Bool, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +p0: T.Pos, +safe: {L.mine(layout, p0) == False{} : Bool},
  +ok: {PF.works_ok(work, w, h, layout, p0) == True{} : Bool}, +q: T.Pos,
  fq: {B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q) == True{} : Bool},
  mq: {B.mine(layout, q) == True{} : Bool}, before: {B.at(Bool, False{}, shown, q) == False{} : Bool}) ->
  {nsm_f(LS{layout, G.flood(n, work, hd, w, h, layout, shown)}, q) == True{} : Bool}:
  nsm_flood.walk(w, h, layout, p0, q, safe, mq,
    PF.flood_path(n, work, hd, w, h, layout, shown, p0, ok, q, before, fq),
    {nsm_f(LS{layout, G.flood(n, work, hd, w, h, layout, shown)}, q) == True{} : Bool})

def nsm_flood.cell(+n: Nat, +work: List<&2, G.Work>, +hd: Bool, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +p0: T.Pos, +safe: {L.mine(layout, p0) == False{} : Bool},
  +ok: {PF.works_ok(work, w, h, layout, p0) == True{} : Bool},
  +ns: {nsm(w, h, layout, shown) == True{} : Bool}, +q: T.Pos, +on: {B.on_board(w, h, q) == True{} : Bool},
  +b: Bool, +be: {Bool.and(B.at(Bool, False{}, G.flood(n, work, hd, w, h, layout, shown), q), B.mine(layout, q)) == b : Bool}) ->
  {nsm_f(LS{layout, G.flood(n, work, hd, w, h, layout, shown)}, q) == True{} : Bool}:
  match b:
    case False{}:
      +F = G.flood(n, work, hd, w, h, layout, shown)
      %Equal.sym(Bool, Bool.and(B.at(Bool, False{}, F, q), B.mine(layout, q)), False{}, be) :
        {Bool.not(_) == True{} : Bool}
      {==}
    case True{}:
      +F = G.flood(n, work, hd, w, h, layout, shown)
      +fq = P.and_true_l(B.at(Bool, False{}, F, q), B.mine(layout, q), be)
      +mq = P.and_true_r(B.at(Bool, False{}, F, q), B.mine(layout, q), be)
      nsm_flood.new(n, work, hd, w, h, layout, shown, p0, safe, ok, q, fq, mq,
        nsm_use(w, h, layout, shown, ns, q, on, mq))

def nsm_flood.cells(+n: Nat, +work: List<&2, G.Work>, +hd: Bool, +w: Nat, +h: Nat, +layout: T.Grid(Bool),
  +shown: T.Grid(Bool), +p0: T.Pos, +safe: {L.mine(layout, p0) == False{} : Bool},
  +ok: {PF.works_ok(work, w, h, layout, p0) == True{} : Bool},
  +ns: {nsm(w, h, layout, shown) == True{} : Bool}, ps: List<&2, T.Pos>,
  +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}) ->
  {PS.allp(~LS, ~nsm_f, LS{layout, G.flood(n, work, hd, w, h, layout, shown)}, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +F = G.flood(n, work, hd, w, h, layout, shown)
      %Equal.sym(Bool, nsm_f(LS{layout, F}, q), True{},
        nsm_flood.cell(n, work, hd, w, h, layout, shown, p0, safe, ok, ns, q,
          PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons),
          Bool.and(B.at(Bool, False{}, F, q), B.mine(layout, q)), {==})) :
        {Bool.and(_, PS.allp(~LS, ~nsm_f, LS{layout, F}, t)) == True{} : Bool}
      nsm_flood.cells(n, work, hd, w, h, layout, shown, p0, safe, ok, ns, t,
        PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))

# A flood from a safe cell reveals no mine.
law nsm_flood:
  for +n: Nat
  for +work: List<&2, G.Work>
  for +hd: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +p0: T.Pos
  for +safe: {L.mine(layout, p0) == False{} : Bool}
  for +ok: {PF.works_ok(work, w, h, layout, p0) == True{} : Bool}
  for +ns: {nsm(w, h, layout, shown) == True{} : Bool}
  {nsm(w, h, layout, G.flood(n, work, hd, w, h, layout, shown)) == True{} : Bool}

def nsm_flood(n, work, hd, w, h, layout, shown, p0, safe, ok, ns):
  nsm_flood.cells(n, work, hd, w, h, layout, shown, p0, safe, ok, ns, B.cells(w, h), PS.cells_on(w, h))

def nsm_blank.cell(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +q: T.Pos) ->
  {nsm_f(LS{layout, B.blank(Bool, w, h, False{})}, q) == True{} : Bool}:
  match q:
    case T.Pos{x, y}:
      %Equal.sym(Bool, B.at(Bool, False{}, B.blank(Bool, w, h, False{}), T.Pos{x, y}), False{}, PL.blank_at(w, h, x, y)) :
        {Bool.not(Bool.and(_, B.mine(layout, T.Pos{x, y}))) == True{} : Bool}
      {==}

def nsm_blank.cells(+w: Nat, +h: Nat, +layout: T.Grid(Bool), ps: List<&2, T.Pos>) ->
  {PS.allp(~LS, ~nsm_f, LS{layout, B.blank(Bool, w, h, False{})}, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case q <> t:
      %Equal.sym(Bool, nsm_f(LS{layout, B.blank(Bool, w, h, False{})}, q), True{}, nsm_blank.cell(w, h, layout, q)) :
        {Bool.and(_, PS.allp(~LS, ~nsm_f, LS{layout, B.blank(Bool, w, h, False{})}, t)) == True{} : Bool}
      nsm_blank.cells(w, h, layout, t)

law nsm_blank:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  {nsm(w, h, layout, B.blank(Bool, w, h, False{})) == True{} : Bool}

def nsm_blank(w, h, layout):
  nsm_blank.cells(w, h, layout, B.cells(w, h))

# Status
# ======

law won_or_playing_won:
  for +b: Bool
  {L.is_won(G.won_or_playing(b)) == b : Bool}

def won_or_playing_won(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law playing_is:
  for +s: T.Status
  for e: {G.is_playing(s) == True{} : Bool}
  {s == T.Playing{} : T.Status}

def playing_is(s, e):
  match s:
    case T.Playing{}:
      {==}
    case T.Won{}:
      Empty.absurd({T.Won{} == T.Playing{} : T.Status}, P.false_ne_true(e))
    case T.Lost{why}:
      Empty.absurd({T.Lost{why} == T.Playing{} : T.Status}, P.false_ne_true(e))

# The invariant
# =============

def calm(+status: T.Status, +w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool)) -> Bool:
  Bool.or(Bool.not(G.is_playing(status)), nsm(w, h, layout, shown))

def Facts(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +status: T.Status) -> Type:
  {B.shaped(Bool, w, h, shown) == True{} : Bool} &
  ({L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool} &
  ({calm(status, w, h, layout, shown) == True{} : Bool} &
   {closed(w, h, layout, shown) == True{} : Bool}))

# What every real game satisfies: the board it was started with, a grid of
# revealed cells of the board's shape, Won exactly when every safe cell is
# revealed, no revealed mine during play, and every revealed zero's
# neighbours revealed.
def Inv(+w: Nat, +h: Nat, +layout: T.Grid(Bool), g: G.Game) -> Type:
  match g:
    case G.Game{gw, gh, gl, shown, flags, status}:
      {gw == w : Nat} & ({gh == h : Nat} & ({gl == layout : T.Grid(Bool)} & Facts(w, h, layout, shown, status)))

def all_safe_cell(+layout: T.Grid(Bool), +shown: T.Grid(Bool), +p: T.Pos, +q: T.Pos,
  mp: {B.mine(layout, p) == True{} : Bool}, +b: Bool, be: {B.same(p, q) == b : Bool}) ->
  {Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q))
    == Bool.or(B.mine(layout, q), B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), q)) : Bool}:
  match b:
    case True{}:
      +mq = {%PG.same_sound(p, q, be) : {B.mine(layout, _) == True{} : Bool}; mp : {B.mine(layout, q) == True{} : Bool}}
      %Equal.sym(Bool, B.mine(layout, q), True{}, mq) :
        {Bool.or(_, B.at(Bool, False{}, shown, q))
          == Bool.or(_, B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), q)) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, B.at(Bool, False{}, B.set_at(Bool, shown, p, True{}), q), B.at(Bool, False{}, shown, q),
        PL.at_set_ne(Bool, shown, p, q, True{}, False{}, be)) :
        {Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)) == Bool.or(B.mine(layout, q), _) : Bool}
      {==}

def all_safe_set_mine.go(+layout: T.Grid(Bool), +shown: T.Grid(Bool), +p: T.Pos,
  +mp: {B.mine(layout, p) == True{} : Bool}, ps: List<&2, T.Pos>) ->
  {G.all_safe.go(layout, B.set_at(Bool, shown, p, True{}), ps) == G.all_safe.go(layout, shown, ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> t:
      +s2 = B.set_at(Bool, shown, p, True{})
      %Equal.sym(Bool, G.all_safe.go(layout, s2, t), G.all_safe.go(layout, shown, t),
        all_safe_set_mine.go(layout, shown, p, mp, t)) :
        {Bool.and(Bool.or(B.mine(layout, q), B.at(Bool, False{}, s2, q)), _)
          == Bool.and(Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)), G.all_safe.go(layout, shown, t)) : Bool}
      %all_safe_cell(layout, shown, p, q, mp, B.same(p, q), {==}) :
        {Bool.and(_, G.all_safe.go(layout, shown, t))
          == Bool.and(Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)), G.all_safe.go(layout, shown, t)) : Bool}
      {==}

law all_safe_set_mine:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +p: T.Pos
  for +mp: {B.mine(layout, p) == True{} : Bool}
  {G.all_safe(w, h, layout, B.set_at(Bool, shown, p, True{})) == G.all_safe(w, h, layout, shown) : Bool}

def all_safe_set_mine(w, h, layout, shown, p, mp):
  all_safe_set_mine.go(layout, shown, p, mp, B.cells(w, h))

# Opening a cell keeps the invariant
# ==================================

def inv_open.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +won: {L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool},
  +cm: {calm(status, w, h, layout, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +p: T.Pos,
  +c: Bool, ce: {Bool.and(G.is_playing(status), G.unrevealed(w, h, shown, p)) == c : Bool},
  +m: Bool, +me: {B.mine(layout, p) == m : Bool}) ->
  Inv(w, h, layout, G.open.go(c, m, G.Game{w, h, layout, shown, flags, status}, p)):
  match c m:
    case False{} _:
      ({==}, ({==}, ({==}, (sh, (won, (cm, cl))))))
    case True{} True{}:
      +st = playing_is(status, P.and_true_l(G.is_playing(status), G.unrevealed(w, h, shown, p), ce))
      +s2 = B.set_at(Bool, shown, p, True{})
      +w0 = {%st : {L.is_won(_) == G.all_safe(w, h, layout, shown) : Bool};
        won : {False{} == G.all_safe(w, h, layout, shown) : Bool}}
      ({==}, ({==}, ({==}, (PL.shaped_set(Bool, w, h, shown, p, True{}, sh),
        (Equal.trans(Bool, False{}, G.all_safe(w, h, layout, shown), G.all_safe(w, h, layout, s2), w0,
          Equal.sym(Bool, G.all_safe(w, h, layout, s2), G.all_safe(w, h, layout, shown),
            all_safe_set_mine(w, h, layout, shown, p, me))),
        ({==}, closed_explode(w, h, layout, shown, p, me, cl)))))))
    case True{} False{}:
      +st = playing_is(status, P.and_true_l(G.is_playing(status), G.unrevealed(w, h, shown, p), ce))
      +start = {[G.Work{p, Nil{}}] : List<&2, G.Work>}
      +cf = B.count_false(shown)
      +hh = G.head_hidden(w, h, shown, start)
      +F = G.flood(cf, start, hh, w, h, layout, shown)
      +ns = {%st : {Bool.or(Bool.not(G.is_playing(_)), nsm(w, h, layout, shown)) == True{} : Bool};
        cm : {nsm(w, h, layout, shown) == True{} : Bool}}
      +ok = {%Equal.sym(Bool, L.same(p, p), True{}, PW.lsame_refl(p)) : {Bool.and(_, True{}) == True{} : Bool};
        {==} : {PF.works_ok(start, w, h, layout, p) == True{} : Bool}}
      +safe = {%PC.mine_eq(layout, p) : {_ == False{} : Bool}; me : {L.mine(layout, p) == False{} : Bool}}
      ({==}, ({==}, ({==}, (PF.flood_shaped(cf, start, hh, w, h, layout, shown, sh),
        (won_or_playing_won(G.all_safe(w, h, layout, F)),
        (%Equal.sym(Bool, nsm(w, h, layout, F), True{}, nsm_flood(cf, start, hh, w, h, layout, shown, p, safe, ok, ns)) :
           {Bool.or(Bool.not(G.is_playing(G.won_or_playing(G.all_safe(w, h, layout, F)))), _) == True{} : Bool};
           PS.or_true_r(Bool.not(G.is_playing(G.won_or_playing(G.all_safe(w, h, layout, F))))),
         closed_flood(cf, start, hh, w, h, layout, shown, sh, cl, {==}, {==})))))))

law inv_open:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +status: T.Status
  for +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool}
  for +won: {L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool}
  for +cm: {calm(status, w, h, layout, shown) == True{} : Bool}
  for +cl: {closed(w, h, layout, shown) == True{} : Bool}
  for +p: T.Pos
  Inv(w, h, layout, G.open(G.Game{w, h, layout, shown, flags, status}, p))

def inv_open(w, h, layout, shown, flags, status, sh, won, cm, cl, p):
  inv_open.go(w, h, layout, shown, flags, status, sh, won, cm, cl, p,
    Bool.and(G.is_playing(status), G.unrevealed(w, h, shown, p)), {==}, B.mine(layout, p), {==})

# Every action keeps the invariant
# ================================

def inv_reveal.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +won: {L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool},
  +cm: {calm(status, w, h, layout, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +p: T.Pos, +f: Bool) ->
  Inv(w, h, layout, G.reveal.go(f, G.Game{w, h, layout, shown, flags, status}, p)):
  match f:
    case True{}:
      ({==}, ({==}, ({==}, (sh, (won, (cm, cl))))))
    case False{}:
      inv_open(w, h, layout, shown, flags, status, sh, won, cm, cl, p)

def inv_flag.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +won: {L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool},
  +cm: {calm(status, w, h, layout, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +p: T.Pos, +c: Bool) ->
  Inv(w, h, layout, G.flag.go(c, G.Game{w, h, layout, shown, flags, status}, p)):
  match c:
    case False{}:
      ({==}, ({==}, ({==}, (sh, (won, (cm, cl))))))
    case True{}:
      ({==}, ({==}, ({==}, (sh, (won, (cm, cl))))))

def inv_assist.safe(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +won: {L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool},
  +cm: {calm(status, w, h, layout, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +m: Maybe<&2, T.Pos>) ->
  Inv(w, h, layout, G.assist.safe(m, G.Game{w, h, layout, shown, flags, status})):
  match m:
    case None{}:
      ({==}, ({==}, ({==}, (sh, (won, (cm, cl))))))
    case Some{p}:
      inv_open(w, h, layout, shown, flags, status, sh, won, cm, cl, p)

def inv_assist.pick(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +won: {L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool},
  +cm: {calm(status, w, h, layout, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool},
  +st: {status == T.Playing{} : T.Status}, +r: Maybe<&2, T.Pos>, +k: Nat) ->
  Inv(w, h, layout, G.assist.pick(r, G.Game{w, h, layout, shown, flags, status}, k)):
  match r:
    case Some{q}:
      ({==}, ({==}, ({==}, (sh,
        ({%st : {L.is_won(_) == G.all_safe(w, h, layout, shown) : Bool};
          won : {False{} == G.all_safe(w, h, layout, shown) : Bool}},
        ({==}, cl))))))
    case None{}:
      inv_assist.safe(w, h, layout, shown, flags, status, sh, won, cm, cl,
        G.safe_cell(G.Game{w, h, layout, shown, flags, status}, k))

def inv_assist.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +sh: {B.shaped(Bool, w, h, shown) == True{} : Bool},
  +won: {L.is_won(status) == G.all_safe(w, h, layout, shown) : Bool},
  +cm: {calm(status, w, h, layout, shown) == True{} : Bool},
  +cl: {closed(w, h, layout, shown) == True{} : Bool}, +c: Bool, ce: {G.is_playing(status) == c : Bool}, +k: Nat) ->
  Inv(w, h, layout, G.assist.go(c, G.Game{w, h, layout, shown, flags, status}, k)):
  match c:
    case False{}:
      ({==}, ({==}, ({==}, (sh, (won, (cm, cl))))))
    case True{}:
      +g0 = {G.Game{w, h, layout, shown, flags, status} : G.Game}
      inv_assist.pick(w, h, layout, shown, flags, status, sh, won, cm, cl, playing_is(status, ce),
        S.solve(G.knowledge(g0)), k)

# Over a game in its general form.
law inv_reveal:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: G.Game
  for inv: Inv(w, h, layout, g)
  for +p: T.Pos
  Inv(w, h, layout, G.reveal(g, p))

def inv_reveal(w, h, layout, g, inv, p):
  match g:
    case G.Game{gw, gh, gl, shown, flags, status}:
      match inv:
        case (ew, rest):
          match rest:
            case (eh, rest2):
              match rest2:
                case (el, facts):
                  match facts:
                    case (sh, f2):
                      match f2:
                        case (won, f3):
                          match f3:
                            case (cm, cl):
                              %Equal.sym(Nat, gw, w, ew) : Inv(w, h, layout, G.reveal(G.Game{_, gh, gl, shown, flags, status}, p))
                              %Equal.sym(Nat, gh, h, eh) : Inv(w, h, layout, G.reveal(G.Game{w, _, gl, shown, flags, status}, p))
                              %Equal.sym(T.Grid(Bool), gl, layout, el) :
                                Inv(w, h, layout, G.reveal(G.Game{w, h, _, shown, flags, status}, p))
                              inv_reveal.go(w, h, layout, shown, flags, status, sh, won, cm, cl, p,
                                G.flagged(G.Game{w, h, layout, shown, flags, status}, p))

law inv_flag:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: G.Game
  for inv: Inv(w, h, layout, g)
  for +p: T.Pos
  Inv(w, h, layout, G.flag(g, p))

def inv_flag(w, h, layout, g, inv, p):
  match g:
    case G.Game{gw, gh, gl, shown, flags, status}:
      match inv:
        case (ew, rest):
          match rest:
            case (eh, rest2):
              match rest2:
                case (el, facts):
                  match facts:
                    case (sh, f2):
                      match f2:
                        case (won, f3):
                          match f3:
                            case (cm, cl):
                              %Equal.sym(Nat, gw, w, ew) : Inv(w, h, layout, G.flag(G.Game{_, gh, gl, shown, flags, status}, p))
                              %Equal.sym(Nat, gh, h, eh) : Inv(w, h, layout, G.flag(G.Game{w, _, gl, shown, flags, status}, p))
                              %Equal.sym(T.Grid(Bool), gl, layout, el) :
                                Inv(w, h, layout, G.flag(G.Game{w, h, _, shown, flags, status}, p))
                              inv_flag.go(w, h, layout, shown, flags, status, sh, won, cm, cl, p,
                                G.can_flag(G.Game{w, h, layout, shown, flags, status}, p))

law inv_assist:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: G.Game
  for inv: Inv(w, h, layout, g)
  for +k: Nat
  Inv(w, h, layout, G.assist(g, k))

def inv_assist(w, h, layout, g, inv, k):
  match g:
    case G.Game{gw, gh, gl, shown, flags, status}:
      match inv:
        case (ew, rest):
          match rest:
            case (eh, rest2):
              match rest2:
                case (el, facts):
                  match facts:
                    case (sh, f2):
                      match f2:
                        case (won, f3):
                          match f3:
                            case (cm, cl):
                              %Equal.sym(Nat, gw, w, ew) : Inv(w, h, layout, G.assist(G.Game{_, gh, gl, shown, flags, status}, k))
                              %Equal.sym(Nat, gh, h, eh) : Inv(w, h, layout, G.assist(G.Game{w, _, gl, shown, flags, status}, k))
                              %Equal.sym(T.Grid(Bool), gl, layout, el) :
                                Inv(w, h, layout, G.assist(G.Game{w, h, _, shown, flags, status}, k))
                              inv_assist.go(w, h, layout, shown, flags, status, sh, won, cm, cl, G.is_playing(status), {==}, k)

law inv_chord:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +ts: List<&2, T.Pos>
  for +g: G.Game
  for inv: Inv(w, h, layout, g)
  Inv(w, h, layout, G.chord_play(ts, g))

def inv_chord(w, h, layout, ts, g, inv):
  match ts:
    case Nil{}:
      inv
    case q <> t:
      inv_chord(w, h, layout, t, G.reveal(g, q), inv_reveal(w, h, layout, g, inv, q))

law inv_step:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: G.Game
  for inv: Inv(w, h, layout, g)
  for +a: T.Action
  Inv(w, h, layout, G.step(g, a))

def inv_step(w, h, layout, g, inv, a):
  match a:
    case T.Reveal{p}:
      inv_reveal(w, h, layout, g, inv, p)
    case T.Chord{p}:
      inv_chord(w, h, layout, G.chord_targets(g, p), g, inv)
    case T.Flag{p}:
      inv_flag(w, h, layout, g, inv, p)
    case T.Assist{k}:
      inv_assist(w, h, layout, g, inv, k)

law inv_play:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +acts: List<&2, T.Action>
  for +g: G.Game
  for inv: Inv(w, h, layout, g)
  Inv(w, h, layout, L.play(acts, g))

def inv_play(w, h, layout, acts, g, inv):
  match acts:
    case Nil{}:
      inv
    case a <> t:
      inv_play(w, h, layout, t, G.step(g, a), inv_step(w, h, layout, g, inv, a))

law inv_fresh:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  Inv(w, h, layout, G.fresh(w, h, layout))

def inv_fresh(w, h, layout):
  +bl = B.blank(Bool, w, h, False{})
  +st = G.won_or_playing(G.all_safe(w, h, layout, bl))
  ({==}, ({==}, ({==}, (PL.blank_shaped(Bool, w, h, False{}),
    (won_or_playing_won(G.all_safe(w, h, layout, bl)),
    (%Equal.sym(Bool, nsm(w, h, layout, bl), True{}, nsm_blank(w, h, layout)) :
       {Bool.or(Bool.not(G.is_playing(st)), _) == True{} : Bool};
       PS.or_true_r(Bool.not(G.is_playing(st))),
     closed_blank(w, h, layout)))))))

# Every real game satisfies the invariant.
law inv_reach:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  Inv(w, h, layout, g)

def inv_reach(w, h, layout, g, r):
  match r:
    case (acts, e):
      %e : Inv(w, h, layout, _)
      inv_play(w, h, layout, acts, G.fresh(w, h, layout), inv_fresh(w, h, layout))
