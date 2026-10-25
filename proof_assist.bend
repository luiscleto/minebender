import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G
import ./solver.bend as S
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG
import ./proof_copy.bend as PC
import ./proof_cells.bend as PS
import ./proof_inv.bend as PI
import ./proof_laws.bend as PW
import ./proof_solver.bend as PV

# Proofs of the two assist laws.

# A safe hidden cell, while one exists
# ====================================

def not_and_false(+a: Bool, +b: Bool, e: {Bool.and(Bool.not(a), Bool.not(b)) == False{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match a b:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, P.true_ne_false(e))

def SafeAt(+layout: T.Grid(Bool), +shown: T.Grid(Bool), +ps: List<&2, T.Pos>) -> Type:
  Exists(T.Pos, p => {G.first_safe(layout, shown, ps) == Some{p} : Maybe<&2, T.Pos>} &
    ({Bool.and(Bool.not(B.mine(layout, p)), Bool.not(B.at(Bool, False{}, shown, p))) == True{} : Bool} &
     {B.contains(ps, p) == True{} : Bool}))

def first_safe.lift(+layout: T.Grid(Bool), +shown: T.Grid(Bool), +q: T.Pos, +t: List<&2, T.Pos>,
  r: SafeAt(layout, shown, t), -hit: Bool, he: {hit == False{} : Bool}) ->
  Exists(T.Pos, p => {G.first_safe.go(q <> t, hit, layout, shown) == Some{p} : Maybe<&2, T.Pos>} &
    ({Bool.and(Bool.not(B.mine(layout, p)), Bool.not(B.at(Bool, False{}, shown, p))) == True{} : Bool} &
     {B.contains(q <> t, p) == True{} : Bool})):
  match r:
    case (+p, pr):
      match pr:
        case (fe, rest):
          match rest:
            case (sf, m):
              %Equal.sym(Bool, hit, False{}, he) :
                Exists(T.Pos, p2 => {G.first_safe.go(q <> t, _, layout, shown) == Some{p2} : Maybe<&2, T.Pos>} &
                  ({Bool.and(Bool.not(B.mine(layout, p2)), Bool.not(B.at(Bool, False{}, shown, p2))) == True{} : Bool} &
                   {B.contains(q <> t, p2) == True{} : Bool}))
              (p, (fe, (sf, PV.or_r(B.same(q, p), B.contains(t, p), m))))

def first_safe.go2(+layout: T.Grid(Bool), +shown: T.Grid(Bool), +q: T.Pos, +t: List<&2, T.Pos>, +hit: Bool,
  he: {Bool.and(Bool.not(B.mine(layout, q)), Bool.not(B.at(Bool, False{}, shown, q))) == hit : Bool},
  e: {Bool.and(Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)), G.all_safe.go(layout, shown, t)) == False{} : Bool},
  ih: {G.all_safe.go(layout, shown, t) == False{} : Bool} -> SafeAt(layout, shown, t)) ->
  Exists(T.Pos, p => {G.first_safe.go(q <> t, hit, layout, shown) == Some{p} : Maybe<&2, T.Pos>} &
    ({Bool.and(Bool.not(B.mine(layout, p)), Bool.not(B.at(Bool, False{}, shown, p))) == True{} : Bool} &
     {B.contains(q <> t, p) == True{} : Bool})):
  match hit:
    case True{}:
      (q, ({==}, (he, PV.or_l(B.same(q, q), B.contains(t, q), PG.same_refl(q)))))
    case False{}:
      first_safe.lift(layout, shown, q, t,
        ih(%not_and_false(B.mine(layout, q), B.at(Bool, False{}, shown, q), he) :
            {Bool.and(_, G.all_safe.go(layout, shown, t)) == False{} : Bool}; e),
        False{}, {==})

# While some safe cell is unrevealed, first_safe finds one.
law first_safe_some:
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +ps: List<&2, T.Pos>
  for e: {G.all_safe.go(layout, shown, ps) == False{} : Bool}
  SafeAt(layout, shown, ps)

def first_safe_some(layout, shown, ps, e):
  match ps:
    case Nil{}:
      Empty.absurd(SafeAt(layout, shown, Nil{}), P.true_ne_false(e))
    case q <> t:
      first_safe.go2(layout, shown, q, t,
        Bool.and(Bool.not(B.mine(layout, q)), Bool.not(B.at(Bool, False{}, shown, q))), {==}, e,
        et => first_safe_some(layout, shown, t, et))

# Pressing the assist when stuck
# ==============================

def stuck_pick.none(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +f: List<&2, T.Pos>,
  +nos: {G.all_safe(w, h, layout, s) == False{} : Bool},
  sa: SafeAt(layout, s, B.cells(w, h))) ->
  Exists(T.Pos, p => {L.mine(layout, p) == False{} : Bool} &
    ({L.hidden(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}), p) == True{} : Bool} &
     {G.assist.safe(G.first_safe(layout, s, B.cells(w, h)), G.Game{w, h, layout, s, f, T.Playing{}})
       == G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p) : G.Game})):
  match sa:
    case (+p, pr):
      match pr:
        case (+fe, rest):
          match rest:
            case (+sf, m):
              +g0 = {G.Game{w, h, layout, s, f, T.Playing{}} : G.Game}
              +nm = P.not_true(B.mine(layout, p), P.and_true_l(Bool.not(B.mine(layout, p)), Bool.not(B.at(Bool, False{}, s, p)), sf))
              +onp = PS.allp_member(~PS.WH, ~PS.onb, PS.WH{w, h}, B.cells(w, h), p, PS.cells_on(w, h), m)
              (p,
                (%PC.mine_eq(layout, p) : {_ == False{} : Bool}; nm,
                 (%Equal.sym(Bool, L.hidden(G.knowledge(g0), p), G.unrevealed(w, h, s, p),
                    PG.know_hidden(w, h, layout, s, f, T.Playing{}, p)) : {_ == True{} : Bool};
                    %Equal.sym(Bool, B.on_board(w, h, p), True{}, onp) :
                      {Bool.and(_, Bool.not(B.at(Bool, False{}, s, p))) == True{} : Bool};
                    P.and_true_r(Bool.not(B.mine(layout, p)), Bool.not(B.at(Bool, False{}, s, p)), sf),
                  %Equal.sym(Maybe<&2, T.Pos>, G.first_safe(layout, s, B.cells(w, h)), Some{p}, fe) :
                    {G.assist.safe(_, g0) == G.open(g0, p) : G.Game};
                  {==})))

def stuck_pick(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +f: List<&2, T.Pos>,
  +nos: {G.all_safe(w, h, layout, s) == False{} : Bool},
  stuck: L.Stuck(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}})),
  +r: Maybe<&2, T.Pos>, re: {S.solve(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}})) == r : Maybe<&2, T.Pos>}) ->
  Exists(T.Pos, p => {L.mine(layout, p) == False{} : Bool} &
    ({L.hidden(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}), p) == True{} : Bool} &
     {G.assist.pick(r, G.Game{w, h, layout, s, f, T.Playing{}}) == G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p) : G.Game})):
  match r:
    case Some{q}:
      +k0 = G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}})
      Empty.absurd(Exists(T.Pos, p => {L.mine(layout, p) == False{} : Bool} &
        ({L.hidden(k0, p) == True{} : Bool} &
         {G.assist.pick(Some{q}, G.Game{w, h, layout, s, f, T.Playing{}}) == G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p) : G.Game})),
        stuck(q, PV.solve_safe(k0, q, re)))
    case None{}:
      stuck_pick.none(w, h, layout, s, f, nos, first_safe_some(layout, s, B.cells(w, h), nos))

def assist_stuck.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  +playing: {G.status(g) == T.Playing{} : T.Status}, stuck: L.Stuck(G.knowledge(g)), c: PW.Canon(w, h, layout, g)) ->
  Exists(T.Pos, p => {L.mine(layout, p) == False{} : Bool} &
    ({L.hidden(G.knowledge(g), p) == True{} : Bool} & {G.step(g, T.Assist{}) == G.open(g, p) : G.Game})):
  match c:
    case (+eg, facts):
      match facts:
        case (sh, f2):
          match f2:
            case (won, f3):
              +s = PW.shown_of(g)
              +f = PW.flags_of(g)
              +gp = {G.Game{w, h, layout, s, f, T.Playing{}} : G.Game}
              %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
                Exists(T.Pos, p => {L.mine(layout, p) == False{} : Bool} &
                  ({L.hidden(G.knowledge(_), p) == True{} : Bool} & {G.step(_, T.Assist{}) == G.open(_, p) : G.Game}))
              %Equal.sym(T.Status, G.status(g), T.Playing{}, playing) :
                Exists(T.Pos, p => {L.mine(layout, p) == False{} : Bool} &
                  ({L.hidden(G.knowledge(G.Game{w, h, layout, s, f, _}), p) == True{} : Bool} &
                   {G.step(G.Game{w, h, layout, s, f, _}, T.Assist{}) == G.open(G.Game{w, h, layout, s, f, _}, p) : G.Game}))
              stuck_pick(w, h, layout, s, f,
                Equal.sym(Bool, False{}, G.all_safe(w, h, layout, s),
                  %playing : {L.is_won(_) == G.all_safe(w, h, layout, s) : Bool}; won),
                {%playing : L.Stuck(G.knowledge(G.Game{w, h, layout, s, f, _}));
                  %eg : L.Stuck(G.knowledge(_)); stuck : L.Stuck(G.knowledge(gp))},
                S.solve(G.knowledge(gp)), {==})

law assist_stuck_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for stuck: L.Stuck(G.knowledge(g))
  Exists(T.Pos, p => {L.mine(layout, p) == False{} : Bool} &
    ({L.hidden(G.knowledge(g), p) == True{} : Bool} & {G.step(g, T.Assist{}) == G.open(g, p) : G.Game}))

def assist_stuck_(w, h, layout, shape, g, r, playing, stuck):
  assist_stuck.k(w, h, layout, g, playing, stuck, PW.canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

# Pressing the assist too early
# =============================

def early_pick(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +f: List<&2, T.Pos>, +q: T.Pos,
  option: L.ProvablySafe(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}), q),
  +r: Maybe<&2, T.Pos>, re: {S.solve(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}})) == r : Maybe<&2, T.Pos>}) ->
  Exists(T.Pos, p => L.ProvablySafe(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}), p) &
    ({G.status(G.assist.pick(r, G.Game{w, h, layout, s, f, T.Playing{}})) == T.Lost{T.AssistTooEarly{p}} : T.Status} &
     {G.knowledge(G.assist.pick(r, G.Game{w, h, layout, s, f, T.Playing{}})) == G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}) : T.Knowledge})):
  match r:
    case Some{p}:
      +k0 = G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}})
      (p, (PV.solve_safe(k0, p, re), ({==}, {==})))
    case None{}:
      +k0 = G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}})
      Empty.absurd(Exists(T.Pos, p => L.ProvablySafe(k0, p) &
        ({G.status(G.assist.pick(None{}, G.Game{w, h, layout, s, f, T.Playing{}})) == T.Lost{T.AssistTooEarly{p}} : T.Status} &
         {G.knowledge(G.assist.pick(None{}, G.Game{w, h, layout, s, f, T.Playing{}})) == k0 : T.Knowledge})),
        PV.solve_stuck(k0, re)(q, option))

def assist_early.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  +playing: {G.status(g) == T.Playing{} : T.Status}, +q: T.Pos, option: L.ProvablySafe(G.knowledge(g), q),
  c: PW.Canon(w, h, layout, g)) ->
  Exists(T.Pos, p => L.ProvablySafe(G.knowledge(g), p) &
    ({G.status(G.step(g, T.Assist{})) == T.Lost{T.AssistTooEarly{p}} : T.Status} &
     {G.knowledge(G.step(g, T.Assist{})) == G.knowledge(g) : T.Knowledge})):
  match c:
    case (+eg, facts):
      +s = PW.shown_of(g)
      +f = PW.flags_of(g)
      +gp = {G.Game{w, h, layout, s, f, T.Playing{}} : G.Game}
      %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
        Exists(T.Pos, p => L.ProvablySafe(G.knowledge(_), p) &
          ({G.status(G.step(_, T.Assist{})) == T.Lost{T.AssistTooEarly{p}} : T.Status} &
           {G.knowledge(G.step(_, T.Assist{})) == G.knowledge(_) : T.Knowledge}))
      %Equal.sym(T.Status, G.status(g), T.Playing{}, playing) :
        Exists(T.Pos, p => L.ProvablySafe(G.knowledge(G.Game{w, h, layout, s, f, _}), p) &
          ({G.status(G.step(G.Game{w, h, layout, s, f, _}, T.Assist{})) == T.Lost{T.AssistTooEarly{p}} : T.Status} &
           {G.knowledge(G.step(G.Game{w, h, layout, s, f, _}, T.Assist{})) == G.knowledge(G.Game{w, h, layout, s, f, _}) : T.Knowledge}))
      early_pick(w, h, layout, s, f, q,
        {%playing : L.ProvablySafe(G.knowledge(G.Game{w, h, layout, s, f, _}), q);
          %eg : L.ProvablySafe(G.knowledge(_), q); option : L.ProvablySafe(G.knowledge(gp), q)},
        S.solve(G.knowledge(gp)), {==})

law assist_too_early_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for +q: T.Pos
  for option: L.ProvablySafe(G.knowledge(g), q)
  Exists(T.Pos, p => L.ProvablySafe(G.knowledge(g), p) &
    ({G.status(G.step(g, T.Assist{})) == T.Lost{T.AssistTooEarly{p}} : T.Status} &
     {G.knowledge(G.step(g, T.Assist{})) == G.knowledge(g) : T.Knowledge}))

def assist_too_early_(w, h, layout, shape, g, r, playing, q, option):
  assist_early.k(w, h, layout, g, playing, q, option, PW.canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))
