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
import ./proof_inv.bend as PI
import ./solver.bend as S

# Proofs of the laws about real games, from the invariant.

def shown_of(g: G.Game) -> T.Grid(Bool):
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      shown

def flags_of(g: G.Game) -> List<&2, T.Pos>:
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      flags

def Canon(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game) -> Type:
  {g == G.Game{w, h, layout, shown_of(g), flags_of(g), G.status(g)} : G.Game} &
  PI.Facts(w, h, layout, shown_of(g), G.status(g))

# A real game in its canonical form, with the facts of the invariant.
law canon:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: G.Game
  for inv: PI.Inv(w, h, layout, g)
  Canon(w, h, layout, g)

def canon(w, h, layout, g, inv):
  match g:
    case G.Game{gw, gh, gl, shown, flags, status}:
      match inv:
        case (ew, rest):
          match rest:
            case (eh, rest2):
              match rest2:
                case (el, facts):
                  %Equal.sym(Nat, gw, w, ew) :
                    {G.Game{_, gh, gl, shown, flags, status} == G.Game{w, h, layout, shown, flags, status} : G.Game} &
                    PI.Facts(w, h, layout, shown, status)
                  %Equal.sym(Nat, gh, h, eh) :
                    {G.Game{w, _, gl, shown, flags, status} == G.Game{w, h, layout, shown, flags, status} : G.Game} &
                    PI.Facts(w, h, layout, shown, status)
                  %Equal.sym(T.Grid(Bool), gl, layout, el) :
                    {G.Game{w, h, _, shown, flags, status} == G.Game{w, h, layout, shown, flags, status} : G.Game} &
                    PI.Facts(w, h, layout, shown, status)
                  ({==}, facts)

# Reading the knowledge of a game
# ===============================

law know_seen:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +status: T.Status
  for +q: T.Pos
  for on: {B.on_board(w, h, q) == True{} : Bool}
  {L.seen(G.knowledge(G.Game{w, h, layout, shown, flags, status}), q) == G.seen_at(w, h, layout, shown, q) : T.Seen}

def know_seen(w, h, layout, shown, flags, status, q, on):
  match q:
    case T.Pos{x, y}:
      PG.know_at(w, h, layout, shown, x, y, on)

law revealed_pick:
  for +c: Bool
  for +m: Bool
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +p: T.Pos
  {Bool.not(L.is_hidden(G.seen_pick(c, m, w, h, layout, p))) == c : Bool}

def revealed_pick(c, m, w, h, layout, p):
  match c m:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}

# On the board, revealed in the knowledge means revealed in the game.
law know_revealed:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +status: T.Status
  for +q: T.Pos
  for +on: {B.on_board(w, h, q) == True{} : Bool}
  {L.revealed(G.knowledge(G.Game{w, h, layout, shown, flags, status}), q) == B.at(Bool, False{}, shown, q) : Bool}

def know_revealed(w, h, layout, shown, flags, status, q, on):
  match q:
    case T.Pos{x, y}:
      +rows = G.know_rows(w, h, layout, shown, List.range(h))
      +p = {T.Pos{x, y} : T.Pos}
      %Equal.sym(Bool, B.on_board(w, h, p), True{}, on) :
        {Bool.and(_, Bool.not(L.is_hidden(L.at(T.Seen, T.Hidden{}, rows, p)))) == B.at(Bool, False{}, shown, p) : Bool}
      %Equal.sym(T.Seen, L.at(T.Seen, T.Hidden{}, rows, p), G.seen_at(w, h, layout, shown, p),
        PG.know_at(w, h, layout, shown, x, y, on)) :
        {Bool.not(L.is_hidden(_)) == B.at(Bool, False{}, shown, p) : Bool}
      revealed_pick(B.at(Bool, False{}, shown, p), B.mine(layout, p), w, h, layout, p)

# The real board
# ==============

law know_row_len:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +y: Nat
  for +xs: List<&2, Nat>
  {List.length(&2, T.Seen, G.know_row(w, h, layout, shown, y, xs)) == List.length(&2, Nat, xs) : Nat}

def know_row_len(w, h, layout, shown, y, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Nat, List.length(&2, T.Seen, G.know_row(w, h, layout, shown, y, t)), List.length(&2, Nat, t),
        know_row_len(w, h, layout, shown, y, t)) : {1n+_ == 1n+List.length(&2, Nat, t) : Nat}
      {==}

law know_rows_len:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +ys: List<&2, Nat>
  {List.length(&2, List<&2, T.Seen>, G.know_rows(w, h, layout, shown, ys)) == List.length(&2, Nat, ys) : Nat}

def know_rows_len(w, h, layout, shown, ys):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      %Equal.sym(Nat, List.length(&2, List<&2, T.Seen>, G.know_rows(w, h, layout, shown, t)), List.length(&2, Nat, t),
        know_rows_len(w, h, layout, shown, t)) : {1n+_ == 1n+List.length(&2, Nat, t) : Nat}
      {==}

law know_rows_wide:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +ys: List<&2, Nat>
  {L.rows_wide(T.Seen, w, G.know_rows(w, h, layout, shown, ys)) == True{} : Bool}

def know_rows_wide(w, h, layout, shown, ys):
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      +row = G.know_row(w, h, layout, shown, y, List.range(w))
      %Equal.sym(Nat, List.length(&2, T.Seen, row), w,
        Equal.trans(Nat, List.length(&2, T.Seen, row), List.length(&2, Nat, List.range(w)), w,
          know_row_len(w, h, layout, shown, y, List.range(w)), P.range_length(w))) :
        {Bool.and(Nat.is_eq(_, w), L.rows_wide(T.Seen, w, G.know_rows(w, h, layout, shown, t))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(w, w), True{}, P.eq_refl(w)) :
        {Bool.and(_, L.rows_wide(T.Seen, w, G.know_rows(w, h, layout, shown, t))) == True{} : Bool}
      know_rows_wide(w, h, layout, shown, t)

law know_shaped:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  {L.shaped(T.Seen, w, h, G.know_rows(w, h, layout, shown, List.range(h))) == True{} : Bool}

def know_shaped(w, h, layout, shown):
  +rows = G.know_rows(w, h, layout, shown, List.range(h))
  %Equal.sym(Nat, List.length(&2, List<&2, T.Seen>, rows), h,
    Equal.trans(Nat, List.length(&2, List<&2, T.Seen>, rows), List.length(&2, Nat, List.range(h)), h,
      know_rows_len(w, h, layout, shown, List.range(h)), P.range_length(h))) :
    {Bool.and(Nat.is_eq(_, h), L.rows_wide(T.Seen, w, rows)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(h, h), True{}, P.eq_refl(h)) : {Bool.and(_, L.rows_wide(T.Seen, w, rows)) == True{} : Bool}
  know_rows_wide(w, h, layout, shown, List.range(h))

def agrees_pick(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +p: T.Pos, +c: Bool, +m: Bool,
  me: {B.mine(layout, p) == m : Bool}) ->
  {L.agrees(w, h, layout, p, G.seen_pick(c, m, w, h, layout, p)) == True{} : Bool}:
  match c m:
    case False{} _:
      {==}
    case True{} True{}:
      %PC.mine_eq(layout, p) : {_ == True{} : Bool}
      me
    case True{} False{}:
      %PC.mine_eq(layout, p) :
        {Bool.and(Bool.not(_), Nat.is_eq(L.adj_mines(w, h, layout, p), B.adj_mines(w, h, layout, p))) == True{} : Bool}
      %Equal.sym(Bool, B.mine(layout, p), False{}, me) :
        {Bool.and(Bool.not(_), Nat.is_eq(L.adj_mines(w, h, layout, p), B.adj_mines(w, h, layout, p))) == True{} : Bool}
      %PC.adj_mines_eq(w, h, layout, p) :
        {Bool.and(True{}, Nat.is_eq(_, B.adj_mines(w, h, layout, p))) == True{} : Bool}
      P.eq_refl(B.adj_mines(w, h, layout, p))

def agrees_cell(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +p: T.Pos,
  on: {B.on_board(w, h, p) == True{} : Bool}) ->
  {L.agrees(w, h, layout, p, L.at(T.Seen, T.Hidden{}, G.know_rows(w, h, layout, shown, List.range(h)), p)) == True{} : Bool}:
  match p:
    case T.Pos{x, y}:
      +q = {T.Pos{x, y} : T.Pos}
      %Equal.sym(T.Seen, L.at(T.Seen, T.Hidden{}, G.know_rows(w, h, layout, shown, List.range(h)), q),
        G.seen_at(w, h, layout, shown, q), PG.know_at(w, h, layout, shown, x, y, on)) :
        {L.agrees(w, h, layout, q, _) == True{} : Bool}
      agrees_pick(w, h, layout, q, B.at(Bool, False{}, shown, q), B.mine(layout, q), {==})

def agrees_all_cells(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), ps: List<&2, T.Pos>,
  +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}) ->
  {L.agrees_all(w, h, G.know_rows(w, h, layout, shown, List.range(h)), layout, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +rows = G.know_rows(w, h, layout, shown, List.range(h))
      %Equal.sym(Bool, L.agrees(w, h, layout, q, L.at(T.Seen, T.Hidden{}, rows, q)), True{},
        agrees_cell(w, h, layout, shown, q, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))) :
        {Bool.and(_, L.agrees_all(w, h, rows, layout, t)) == True{} : Bool}
      agrees_all_cells(w, h, layout, shown, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))

law bridge_canon:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +shown: T.Grid(Bool)
  for +flags: List<&2, T.Pos>
  for +status: T.Status
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  {L.consistent(G.knowledge(G.Game{w, h, layout, shown, flags, status}), layout) == True{} : Bool}

def bridge_canon(w, h, layout, shown, flags, status, shape):
  +rows = G.know_rows(w, h, layout, shown, List.range(h))
  PW.and4_intro(L.shaped(Bool, w, h, layout), L.shaped(T.Seen, w, h, rows),
    Nat.is_eq(L.total_mines(layout), B.total_mines(layout)), L.agrees_all(w, h, rows, layout, L.cells(w, h)),
    shape, know_shaped(w, h, layout, shown),
    %PC.total_mines_eq(layout) : {Nat.is_eq(_, B.total_mines(layout)) == True{} : Bool};
      P.eq_refl(B.total_mines(layout)),
    %PC.cells_eq(w, h) : {L.agrees_all(w, h, rows, layout, _) == True{} : Bool};
      agrees_all_cells(w, h, layout, shown, B.cells(w, h), PS.cells_on(w, h)))

def bridge.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}, c: Canon(w, h, layout, g)) ->
  {L.consistent(G.knowledge(g), layout) == True{} : Bool}:
  match c:
    case (eg, facts):
      %Equal.sym(G.Game, g, G.Game{w, h, layout, shown_of(g), flags_of(g), G.status(g)}, eg) :
        {L.consistent(G.knowledge(_), layout) == True{} : Bool}
      bridge_canon(w, h, layout, shown_of(g), flags_of(g), G.status(g), shape)

law bridge_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  {L.consistent(G.knowledge(g), layout) == True{} : Bool}

def bridge_(w, h, layout, shape, g, r):
  bridge.k(w, h, layout, g, shape, canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

# Winning
# =======

def safe_rev_cell(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +q: T.Pos, +on: {B.on_board(w, h, q) == True{} : Bool}) ->
  {Bool.or(L.mine(layout, q), L.revealed(G.knowledge(G.Game{w, h, layout, shown, flags, status}), q))
    == Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)) : Bool}:
  %PC.mine_eq(layout, q) :
    {Bool.or(_, L.revealed(G.knowledge(G.Game{w, h, layout, shown, flags, status}), q))
      == Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)) : Bool}
  %Equal.sym(Bool, L.revealed(G.knowledge(G.Game{w, h, layout, shown, flags, status}), q), B.at(Bool, False{}, shown, q),
    know_revealed(w, h, layout, shown, flags, status, q, on)) :
    {Bool.or(B.mine(layout, q), _) == Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)) : Bool}
  {==}

def safe_rev_all(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, ps: List<&2, T.Pos>, +ons: {PS.allp(~PS.WH, ~PS.onb, PS.WH{w, h}, ps) == True{} : Bool}) ->
  {L.all_safe_revealed.go(G.knowledge(G.Game{w, h, layout, shown, flags, status}), layout, ps)
    == G.all_safe.go(layout, shown, ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +t:
      +v = G.knowledge(G.Game{w, h, layout, shown, flags, status})
      %Equal.sym(Bool, Bool.or(L.mine(layout, q), L.revealed(v, q)), Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)),
        safe_rev_cell(w, h, layout, shown, flags, status, q, PS.allp_head(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))) :
        {Bool.and(_, L.all_safe_revealed.go(v, layout, t))
          == Bool.and(Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)), G.all_safe.go(layout, shown, t)) : Bool}
      %Equal.sym(Bool, L.all_safe_revealed.go(v, layout, t), G.all_safe.go(layout, shown, t),
        safe_rev_all(w, h, layout, shown, flags, status, t, PS.allp_tail(~PS.WH, ~PS.onb, PS.WH{w, h}, q, t, ons))) :
        {Bool.and(Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)), _)
          == Bool.and(Bool.or(B.mine(layout, q), B.at(Bool, False{}, shown, q)), G.all_safe.go(layout, shown, t)) : Bool}
      {==}

def won_iff.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game, c: Canon(w, h, layout, g)) ->
  {L.is_won(G.status(g)) == L.all_safe_revealed(G.knowledge(g), layout) : Bool}:
  match c:
    case (eg, facts):
      match facts:
        case (sh, f2):
          match f2:
            case (won, f3):
              %Equal.sym(G.Game, g, G.Game{w, h, layout, shown_of(g), flags_of(g), G.status(g)}, eg) :
                {L.is_won(G.status(_)) == L.all_safe_revealed(G.knowledge(_), layout) : Bool}
              +s = shown_of(g)
              +f = flags_of(g)
              +st = G.status(g)
              %PC.cells_eq(w, h) :
                {L.is_won(st) == L.all_safe_revealed.go(G.knowledge(G.Game{w, h, layout, s, f, st}), layout, _) : Bool}
              %Equal.sym(Bool, L.all_safe_revealed.go(G.knowledge(G.Game{w, h, layout, s, f, st}), layout, B.cells(w, h)),
                G.all_safe.go(layout, s, B.cells(w, h)), safe_rev_all(w, h, layout, s, f, st, B.cells(w, h), PS.cells_on(w, h))) :
                {L.is_won(st) == _ : Bool}
              won

law won_iff_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  {L.is_won(G.status(g)) == L.all_safe_revealed(G.knowledge(g), layout) : Bool}

def won_iff_(w, h, layout, shape, g, r):
  won_iff.k(w, h, layout, g, canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

# Flags
# =====

law flags_hidden_:
  for +g: G.Game
  for +q: T.Pos
  for flag: {G.flagged(g, q) == True{} : Bool}
  {L.hidden(G.knowledge(g), q) == True{} : Bool}

def flags_hidden_(g, q, flag):
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      %Equal.sym(Bool, L.hidden(G.knowledge(G.Game{w, h, layout, shown, flags, status}), q), G.unrevealed(w, h, shown, q),
        PG.know_hidden(w, h, layout, shown, flags, status, q)) : {_ == True{} : Bool}
      P.and_true_l(G.unrevealed(w, h, shown, q), B.contains(flags, q), flag)

# Revealed cells stay revealed
# ============================

def open_mono.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +shown: T.Grid(Bool), +flags: List<&2, T.Pos>,
  +status: T.Status, +p: T.Pos, +q: T.Pos, s: {B.at(Bool, False{}, shown, q) == True{} : Bool}, +c: Bool, +m: Bool) ->
  {B.at(Bool, False{}, shown_of(G.open.go(c, m, G.Game{w, h, layout, shown, flags, status}, p)), q) == True{} : Bool}:
  match c m:
    case False{} _:
      s
    case True{} True{}:
      PF.at_set_mono(shown, p, q, s)
    case True{} False{}:
      +start = {[G.Work{p, Nil{}}] : List<&2, G.Work>}
      PF.flood_mono(B.count_false(shown), start, G.head_hidden(w, h, shown, start), w, h, layout, shown, q, s)

law open_mono:
  for +g: G.Game
  for +p: T.Pos
  for +q: T.Pos
  for s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}
  {B.at(Bool, False{}, shown_of(G.open(g, p)), q) == True{} : Bool}

def open_mono(g, p, q, s):
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      open_mono.go(w, h, layout, shown, flags, status, p, q, s,
        Bool.and(G.is_playing(status), G.unrevealed(w, h, shown, p)), B.mine(layout, p))

def reveal_mono.go(+g: G.Game, +p: T.Pos, +q: T.Pos, s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}, +f: Bool) ->
  {B.at(Bool, False{}, shown_of(G.reveal.go(f, g, p)), q) == True{} : Bool}:
  match f:
    case True{}:
      s
    case False{}:
      open_mono(g, p, q, s)

law reveal_mono:
  for +g: G.Game
  for +p: T.Pos
  for +q: T.Pos
  for s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}
  {B.at(Bool, False{}, shown_of(G.reveal(g, p)), q) == True{} : Bool}

def reveal_mono(g, p, q, s):
  reveal_mono.go(g, p, q, s, G.flagged(g, p))

law chord_mono:
  for +ts: List<&2, T.Pos>
  for +g: G.Game
  for +q: T.Pos
  for s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}
  {B.at(Bool, False{}, shown_of(G.chord_play(ts, g)), q) == True{} : Bool}

def chord_mono(ts, g, q, s):
  match ts:
    case Nil{}:
      s
    case p <> t:
      chord_mono(t, G.reveal(g, p), q, reveal_mono(g, p, q, s))

def flag_mono.go(+c: Bool, +g: G.Game, +p: T.Pos, +q: T.Pos, s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}) ->
  {B.at(Bool, False{}, shown_of(G.flag.go(c, g, p)), q) == True{} : Bool}:
  match c:
    case False{}:
      s
    case True{}:
      match g:
        case G.Game{w, h, layout, shown, flags, status}:
          s

def assist_mono.safe(+g: G.Game, +q: T.Pos, s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool},
  +m: Maybe<&2, T.Pos>) -> {B.at(Bool, False{}, shown_of(G.assist.safe(m, g)), q) == True{} : Bool}:
  match m:
    case None{}:
      s
    case Some{p}:
      open_mono(g, p, q, s)

def assist_mono.pick(+r: Maybe<&2, T.Pos>, +g: G.Game, +q: T.Pos, s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}, +k: Nat) ->
  {B.at(Bool, False{}, shown_of(G.assist.pick(r, g, k)), q) == True{} : Bool}:
  match r:
    case Some{x}:
      match g:
        case G.Game{w, h, layout, shown, flags, status}:
          s
    case None{}:
      assist_mono.safe(g, q, s, G.safe_cell(g, k))

def assist_mono.go(+g: G.Game, +q: T.Pos, s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}, +c: Bool, +k: Nat) ->
  {B.at(Bool, False{}, shown_of(G.assist.go(c, g, k)), q) == True{} : Bool}:
  match c:
    case False{}:
      s
    case True{}:
      assist_mono.pick(S.solve(G.knowledge(g)), g, q, s, k)

law step_mono:
  for +g: G.Game
  for +a: T.Action
  for +q: T.Pos
  for s: {B.at(Bool, False{}, shown_of(g), q) == True{} : Bool}
  {B.at(Bool, False{}, shown_of(G.step(g, a)), q) == True{} : Bool}

def step_mono(g, a, q, s):
  match a:
    case T.Reveal{p}:
      reveal_mono(g, p, q, s)
    case T.Chord{p}:
      chord_mono(G.chord_targets(g, p), g, q, s)
    case T.Flag{p}:
      flag_mono.go(G.can_flag(g, p), g, p, q, s)
    case T.Assist{k}:
      assist_mono.go(g, q, s, G.is_playing(G.status(g)), k)

law inv_of:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: G.Game
  for +acts: List<&2, T.Action>
  for +e: {L.play(acts, G.fresh(w, h, layout)) == g : G.Game}
  PI.Inv(w, h, layout, g)

def inv_of(w, h, layout, g, acts, e):
  %e : PI.Inv(w, h, layout, _)
  PI.inv_play(w, h, layout, acts, G.fresh(w, h, layout), PI.inv_fresh(w, h, layout))

# A revealed cell of the knowledge is on the board and revealed in the game.
def vis_parts(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +f: List<&2, T.Pos>, +st: T.Status,
  +q: T.Pos, vis: {L.revealed(G.knowledge(G.Game{w, h, layout, s, f, st}), q) == True{} : Bool}) ->
  {B.on_board(w, h, q) == True{} : Bool}:
  match q:
    case T.Pos{x, y}:
      P.and_true_l(L.on_board(w, h, T.Pos{x, y}),
        Bool.not(L.is_hidden(L.at(T.Seen, T.Hidden{}, G.know_rows(w, h, layout, s, List.range(h)), T.Pos{x, y}))), vis)

def monotone.k2(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game, +a: T.Action, +q: T.Pos,
  vis: {L.revealed(G.knowledge(g), q) == True{} : Bool},
  +eg: {g == G.Game{w, h, layout, shown_of(g), flags_of(g), G.status(g)} : G.Game},
  eg2: {G.step(g, a) == G.Game{w, h, layout, shown_of(G.step(g, a)), flags_of(G.step(g, a)), G.status(G.step(g, a))} : G.Game}) ->
  {L.seen(G.knowledge(G.step(g, a)), q) == L.seen(G.knowledge(g), q) : T.Seen}:
  +s1 = shown_of(g)
  +f1 = flags_of(g)
  +t1 = G.status(g)
  +g2 = G.step(g, a)
  +s2 = shown_of(g2)
  +f2 = flags_of(g2)
  +t2 = G.status(g2)
  +vis1 = {%eg : {L.revealed(G.knowledge(_), q) == True{} : Bool};
    vis : {L.revealed(G.knowledge(G.Game{w, h, layout, s1, f1, t1}), q) == True{} : Bool}}
  +on = vis_parts(w, h, layout, s1, f1, t1, q, vis1)
  +at1 = {%know_revealed(w, h, layout, s1, f1, t1, q, on) : {_ == True{} : Bool};
    vis1 : {B.at(Bool, False{}, s1, q) == True{} : Bool}}
  +at2 = step_mono(g, a, q, at1)
  %Equal.sym(G.Game, g2, G.Game{w, h, layout, s2, f2, t2}, eg2) :
    {L.seen(G.knowledge(_), q) == L.seen(G.knowledge(g), q) : T.Seen}
  %Equal.sym(G.Game, g, G.Game{w, h, layout, s1, f1, t1}, eg) :
    {L.seen(G.knowledge(G.Game{w, h, layout, s2, f2, t2}), q) == L.seen(G.knowledge(_), q) : T.Seen}
  %Equal.sym(T.Seen, L.seen(G.knowledge(G.Game{w, h, layout, s2, f2, t2}), q), G.seen_at(w, h, layout, s2, q),
    know_seen(w, h, layout, s2, f2, t2, q, on)) :
    {_ == L.seen(G.knowledge(G.Game{w, h, layout, s1, f1, t1}), q) : T.Seen}
  %Equal.sym(T.Seen, L.seen(G.knowledge(G.Game{w, h, layout, s1, f1, t1}), q), G.seen_at(w, h, layout, s1, q),
    know_seen(w, h, layout, s1, f1, t1, q, on)) :
    {G.seen_at(w, h, layout, s2, q) == _ : T.Seen}
  %Equal.sym(Bool, B.at(Bool, False{}, s2, q), True{}, at2) :
    {G.seen_pick(_, B.mine(layout, q), w, h, layout, q) == G.seen_pick(B.at(Bool, False{}, s1, q), B.mine(layout, q), w, h, layout, q) : T.Seen}
  %Equal.sym(Bool, B.at(Bool, False{}, s1, q), True{}, at1) :
    {G.seen_pick(True{}, B.mine(layout, q), w, h, layout, q) == G.seen_pick(_, B.mine(layout, q), w, h, layout, q) : T.Seen}
  {==}

def monotone.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game, +a: T.Action, +q: T.Pos,
  vis: {L.revealed(G.knowledge(g), q) == True{} : Bool}, c1: Canon(w, h, layout, g),
  c2: Canon(w, h, layout, G.step(g, a))) ->
  {L.seen(G.knowledge(G.step(g, a)), q) == L.seen(G.knowledge(g), q) : T.Seen}:
  match c1:
    case (eg, f1):
      match c2:
        case (eg2, f2):
          monotone.k2(w, h, layout, g, a, q, vis, eg, eg2)

def monotone.r(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game, +a: T.Action, +q: T.Pos,
  vis: {L.revealed(G.knowledge(g), q) == True{} : Bool}, +acts: List<&2, T.Action>,
  +e: {L.play(acts, G.fresh(w, h, layout)) == g : G.Game}) ->
  {L.seen(G.knowledge(G.step(g, a)), q) == L.seen(G.knowledge(g), q) : T.Seen}:
  monotone.k(w, h, layout, g, a, q, vis, canon(w, h, layout, g, inv_of(w, h, layout, g, acts, e)),
    canon(w, h, layout, G.step(g, a), PI.inv_step(w, h, layout, g, inv_of(w, h, layout, g, acts, e), a)))

law monotone_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +a: T.Action
  for +q: T.Pos
  for vis: {L.revealed(G.knowledge(g), q) == True{} : Bool}
  {L.seen(G.knowledge(G.step(g, a)), q) == L.seen(G.knowledge(g), q) : T.Seen}

def monotone_(w, h, layout, shape, g, r, a, q, vis):
  match r:
    case (acts, e):
      monotone.r(w, h, layout, g, a, q, vis, acts, e)

# Opening cells
# =============

def mine_on.col(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +x: Nat, +y: Nat,
  +sh: {B.shaped(Bool, w, h, layout) == True{} : Bool}, yh: {Nat.is_lt(y, h) == True{} : Bool},
  m: {Maybe.default(&2, Bool, List.get(&2, Bool, PL.row_of(Bool, layout, y), x), False{}) == True{} : Bool},
  +b: Bool, be: {Nat.is_lt(x, w) == b : Bool}) -> {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(x, w), True{}, be) : {Bool.and(_, Nat.is_lt(y, h)) == True{} : Bool}
      yh
    case False{}:
      +row = PL.row_of(Bool, layout, y)
      Empty.absurd({B.on_board(w, h, T.Pos{x, y}) == True{} : Bool},
        P.false_ne_true(%P.get_out(Bool, row, x,
          %Equal.sym(Nat, List.length(&2, Bool, row), w, PL.row_in_len(Bool, w, h, layout, y, sh, yh)) :
            {Nat.is_lt(x, _) == False{} : Bool}; be) :
          {Maybe.default(&2, Bool, _, False{}) == True{} : Bool}; m))

def mine_on.row(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +x: Nat, +y: Nat,
  +sh: {B.shaped(Bool, w, h, layout) == True{} : Bool},
  m: {B.mine(layout, T.Pos{x, y}) == True{} : Bool}, +b: Bool, +be: {Nat.is_lt(y, h) == b : Bool}) ->
  {B.on_board(w, h, T.Pos{x, y}) == True{} : Bool}:
  match b:
    case True{}:
      mine_on.col(w, h, layout, x, y, sh, be,
        %Equal.sym(Maybe<&2, List<&2, Bool>>, List.get(&2, List<&2, Bool>, layout, y), Some{PL.row_of(Bool, layout, y)},
          PL.row_in_get(Bool, w, h, layout, y, sh, be)) :
          {Maybe.default(&2, Bool, List.get(&2, Bool, Maybe.default(&2, List<&2, Bool>, _, Nil{}), x), False{}) == True{} : Bool};
        m, Nat.is_lt(x, w), {==})
    case False{}:
      Empty.absurd({B.on_board(w, h, T.Pos{x, y}) == True{} : Bool},
        P.false_ne_true(%P.get_out(List<&2, Bool>, layout, y,
          %Equal.sym(Nat, List.length(&2, List<&2, Bool>, layout), h, PL.shaped_len(Bool, w, h, layout, sh)) :
            {Nat.is_lt(y, _) == False{} : Bool}; be) :
          {Maybe.default(&2, Bool, List.get(&2, Bool, Maybe.default(&2, List<&2, Bool>, _, Nil{}), x), False{})
            == True{} : Bool}; m))

# A mine of a w-by-h layout is on the board.
law mine_on:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +sh: {B.shaped(Bool, w, h, layout) == True{} : Bool}
  for +p: T.Pos
  for m: {B.mine(layout, p) == True{} : Bool}
  {B.on_board(w, h, p) == True{} : Bool}

def mine_on(w, h, layout, sh, p, m):
  match p:
    case T.Pos{x, y}:
      mine_on.row(w, h, layout, x, y, sh, m, Nat.is_lt(y, h), {==})

# In a closed grid, a zero walk from a revealed cell ends at a revealed cell.
law path_closed:
  for +path: List<&2, T.Pos>
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +g: T.Grid(Bool)
  for +cl: {PI.closed(w, h, layout, g) == True{} : Bool}
  for +s: T.Pos
  for +q: T.Pos
  for gs: {B.at(Bool, False{}, g, s) == True{} : Bool}
  for +wk: {L.zero_walk(path, w, h, layout, s, q) == True{} : Bool}
  {B.at(Bool, False{}, g, q) == True{} : Bool}

def path_closed(path, w, h, layout, g, cl, s, q, gs, wk):
  match path:
    case Nil{}:
      %PW.lsame_sound(s, q, wk) : {B.at(Bool, False{}, g, _) == True{} : Bool}
      gs
    case r <> t:
      +zs = L.zero(w, h, layout, s)
      +sr = L.adjacent(s, r)
      +orr = L.on_board(w, h, r)
      +rest = L.zero_walk(t, w, h, layout, r, q)
      +zsB = {%Equal.sym(Bool, B.zero(w, h, layout, s), L.zero(w, h, layout, s), PC.zero_eq(w, h, layout, s)) :
        {_ == True{} : Bool}; PW.and4_a(zs, sr, orr, rest, wk) :
        {B.zero(w, h, layout, s) == True{} : Bool}}
      +onsB = P.and_true_l(B.on_board(w, h, s), Bool.not(B.mine(layout, s)),
        P.and_true_l(Bool.and(B.on_board(w, h, s), Bool.not(B.mine(layout, s))),
          Nat.is_eq(B.adj_mines(w, h, layout, s), 0n), zsB))
      +rm = PS.neighbours_member(w, h, s, r,
        %Equal.sym(Bool, B.on_board(w, h, r), L.on_board(w, h, r), PC.on_board_eq(w, h, r)) :
          {_ == True{} : Bool}; PW.and4_c(zs, sr, orr, rest, wk),
        %Equal.sym(Bool, B.adjacent(s, r), L.adjacent(s, r), PC.adjacent_eq(s, r)) :
          {_ == True{} : Bool}; PW.and4_b(zs, sr, orr, rest, wk))
      path_closed(t, w, h, layout, g, cl, r, q,
        PI.closed_use(w, h, layout, g, cl, s, onsB, gs, zsB, r, rm), PW.and4_d(zs, sr, orr, rest, wk))

def unrev_true(+w: Nat, +h: Nat, +shown: T.Grid(Bool), +p: T.Pos, on: {B.on_board(w, h, p) == True{} : Bool},
  hid: {B.at(Bool, False{}, shown, p) == False{} : Bool}) -> {G.unrevealed(w, h, shown, p) == True{} : Bool}:
  %Equal.sym(Bool, B.on_board(w, h, p), True{}, on) :
    {Bool.and(_, Bool.not(B.at(Bool, False{}, shown, p))) == True{} : Bool}
  %Equal.sym(Bool, B.at(Bool, False{}, shown, p), False{}, hid) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
  {==}

def is_lost_wop(+b: Bool) -> {L.is_lost(G.won_or_playing(b)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def start_ok(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +p: T.Pos) ->
  {PF.works_ok({[G.Work{p, Nil{}}] : List<&2, G.Work>}, w, h, layout, p) == True{} : Bool}:
  %Equal.sym(Bool, L.same(p, p), True{}, PW.lsame_refl(p)) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def start_has(+p: T.Pos) -> {PF.wcontains({[G.Work{p, Nil{}}] : List<&2, G.Work>}, p) == True{} : Bool}:
  %Equal.sym(Bool, B.same(p, p), True{}, PG.same_refl(p)) : {Bool.or(_, False{}) == True{} : Bool}
  {==}

# Opening a mine
# --------------

law open_mine_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +shL: {B.shaped(Bool, w, h, layout) == True{} : Bool}
  for +shS: {B.shaped(Bool, w, h, s) == True{} : Bool}
  for +ns: {PI.nsm(w, h, layout, s) == True{} : Bool}
  for +p: T.Pos
  for +bm: {B.mine(layout, p) == True{} : Bool}
  {G.status(G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p)) == T.Lost{T.Exploded{p}} : T.Status} &
  {L.seen(G.knowledge(G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p)), p) == T.Boom{} : T.Seen}

def open_mine_c(w, h, layout, s, f, shL, shS, ns, p, bm):
  +g0 = {G.Game{w, h, layout, s, f, T.Playing{}} : G.Game}
  +on = mine_on(w, h, layout, shL, p, bm)
  +u = unrev_true(w, h, s, p, on, PI.nsm_use(w, h, layout, s, ns, p, on, bm))
  +s2 = B.set_at(Bool, s, p, True{})
  %Equal.sym(Bool, G.unrevealed(w, h, s, p), True{}, u) :
    {G.status(G.open.go(_, B.mine(layout, p), g0, p)) == T.Lost{T.Exploded{p}} : T.Status} &
    {L.seen(G.knowledge(G.open.go(_, B.mine(layout, p), g0, p)), p) == T.Boom{} : T.Seen}
  %Equal.sym(Bool, B.mine(layout, p), True{}, bm) :
    {G.status(G.open.go(True{}, _, g0, p)) == T.Lost{T.Exploded{p}} : T.Status} &
    {L.seen(G.knowledge(G.open.go(True{}, _, g0, p)), p) == T.Boom{} : T.Seen}
  ({==},
    %Equal.sym(T.Seen, L.seen(G.knowledge(G.Game{w, h, layout, s2, f, T.Lost{T.Exploded{p}}}), p),
      G.seen_at(w, h, layout, s2, p), know_seen(w, h, layout, s2, f, T.Lost{T.Exploded{p}}, p, on)) :
      {_ == T.Boom{} : T.Seen};
    %Equal.sym(Bool, B.at(Bool, False{}, s2, p), True{}, PF.at_set_on(w, h, s, p, shS, on)) :
      {G.seen_pick(_, B.mine(layout, p), w, h, layout, p) == T.Boom{} : T.Seen};
    %Equal.sym(Bool, B.mine(layout, p), True{}, bm) :
      {G.seen_pick(True{}, _, w, h, layout, p) == T.Boom{} : T.Seen};
    {==})

# Opening a safe cell
# -------------------

def open_safe_c.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +f: List<&2, T.Pos>, +p: T.Pos,
  bm: {B.mine(layout, p) == False{} : Bool}, +c: Bool) ->
  {L.is_lost(G.status(G.open.go(c, B.mine(layout, p), G.Game{w, h, layout, s, f, T.Playing{}}, p))) == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +g0 = {G.Game{w, h, layout, s, f, T.Playing{}} : G.Game}
      %Equal.sym(Bool, B.mine(layout, p), False{}, bm) :
        {L.is_lost(G.status(G.open.go(True{}, _, g0, p))) == False{} : Bool}
      +start = {[G.Work{p, Nil{}}] : List<&2, G.Work>}
      is_lost_wop(G.all_safe(w, h, layout,
        G.flood(B.count_false(s), start, G.head_hidden(w, h, s, start), w, h, layout, s)))

law open_safe_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +p: T.Pos
  for bm: {B.mine(layout, p) == False{} : Bool}
  {L.is_lost(G.status(G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p))) == False{} : Bool}

def open_safe_c(w, h, layout, s, f, p, bm):
  open_safe_c.go(w, h, layout, s, f, p, bm, G.unrevealed(w, h, s, p))

# The flood, completely and exactly
# ---------------------------------

def flood_complete_c.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +f: List<&2, T.Pos>,
  +shS: {B.shaped(Bool, w, h, s) == True{} : Bool}, +cl: {PI.closed(w, h, layout, s) == True{} : Bool},
  +p: T.Pos, +on: {B.on_board(w, h, p) == True{} : Bool}, +q: T.Pos, +onq: {B.on_board(w, h, q) == True{} : Bool},
  +path: List<&2, T.Pos>, +wk: {L.zero_walk(path, w, h, layout, p, q) == True{} : Bool},
  +c: Bool, ce: {G.unrevealed(w, h, s, p) == c : Bool}, +m: Bool, me: {B.mine(layout, p) == m : Bool}) ->
  {L.revealed(G.knowledge(G.open.go(c, m, G.Game{w, h, layout, s, f, T.Playing{}}, p)), q) == True{} : Bool}:
  match c m:
    case False{} _:
      %Equal.sym(Bool, L.revealed(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}), q), B.at(Bool, False{}, s, q),
        know_revealed(w, h, layout, s, f, T.Playing{}, q, onq)) : {_ == True{} : Bool}
      path_closed(path, w, h, layout, s, cl, p, q, PF.unrev_shown(w, h, s, p, ce, on), wk)
    case True{} True{}:
      +s2 = B.set_at(Bool, s, p, True{})
      %Equal.sym(Bool, L.revealed(G.knowledge(G.Game{w, h, layout, s2, f, T.Lost{T.Exploded{p}}}), q), B.at(Bool, False{}, s2, q),
        know_revealed(w, h, layout, s2, f, T.Lost{T.Exploded{p}}, q, onq)) : {_ == True{} : Bool}
      path_closed(path, w, h, layout, s2, PI.closed_explode(w, h, layout, s, p, me, cl), p, q,
        PF.at_set_on(w, h, s, p, shS, on), wk)
    case True{} False{}:
      +start = {[G.Work{p, Nil{}}] : List<&2, G.Work>}
      +cf = B.count_false(s)
      +hh = G.head_hidden(w, h, s, start)
      +fl = G.flood(cf, start, hh, w, h, layout, s)
      +st = G.won_or_playing(G.all_safe(w, h, layout, fl))
      %Equal.sym(Bool, L.revealed(G.knowledge(G.Game{w, h, layout, fl, f, st}), q), B.at(Bool, False{}, fl, q),
        know_revealed(w, h, layout, fl, f, st, q, onq)) : {_ == True{} : Bool}
      path_closed(path, w, h, layout, fl, PI.closed_flood(cf, start, hh, w, h, layout, s, shS, cl, {==}, {==}), p, q,
        PF.flood_work(cf, start, hh, w, h, layout, s, shS, {==}, {==}, p, on, start_has(p)), wk)

law flood_complete_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +shS: {B.shaped(Bool, w, h, s) == True{} : Bool}
  for +cl: {PI.closed(w, h, layout, s) == True{} : Bool}
  for +p: T.Pos
  for +on: {L.on_board(w, h, p) == True{} : Bool}
  for +q: T.Pos
  for +path: List<&2, T.Pos>
  for +wk: {L.zero_walk(path, w, h, layout, p, q) == True{} : Bool}
  {L.revealed(G.knowledge(G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p)), q) == True{} : Bool}

def flood_complete_c(w, h, layout, s, f, shS, cl, p, on, q, path, wk):
  +onB = {%Equal.sym(Bool, B.on_board(w, h, p), L.on_board(w, h, p), PC.on_board_eq(w, h, p)) : {_ == True{} : Bool};
    on : {B.on_board(w, h, p) == True{} : Bool}}
  +onq = {%Equal.sym(Bool, B.on_board(w, h, q), L.on_board(w, h, q), PC.on_board_eq(w, h, q)) : {_ == True{} : Bool};
    PW.walk_on(path, w, h, layout, p, q, wk, on) : {B.on_board(w, h, q) == True{} : Bool}}
  flood_complete_c.go(w, h, layout, s, f, shS, cl, p, onB, q, onq, path, wk,
    G.unrevealed(w, h, s, p), {==}, B.mine(layout, p), {==})

def exact_explode(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +p: T.Pos, +q: T.Pos,
  hidq: {B.at(Bool, False{}, s, q) == False{} : Bool},
  after: {B.at(Bool, False{}, B.set_at(Bool, s, p, True{}), q) == True{} : Bool},
  +b: Bool, be: {B.same(p, q) == b : Bool}) -> PF.Walk(w, h, layout, p, q):
  match b:
    case True{}:
      (Nil{}, %PC.same_eq(p, q) : {_ == True{} : Bool}; be)
    case False{}:
      PF.both_absurd(PF.Walk(w, h, layout, p, q), B.at(Bool, False{}, s, q), hidq,
        %PL.at_set_ne(Bool, s, p, q, True{}, False{}, be) : {_ == True{} : Bool}; after)

def flood_exact_c.go(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +s: T.Grid(Bool), +f: List<&2, T.Pos>,
  +p: T.Pos, +q: T.Pos, +onq: {B.on_board(w, h, q) == True{} : Bool},
  +hidq: {B.at(Bool, False{}, s, q) == False{} : Bool},
  +c: Bool, +m: Bool,
  after: {L.revealed(G.knowledge(G.open.go(c, m, G.Game{w, h, layout, s, f, T.Playing{}}, p)), q) == True{} : Bool}) ->
  PF.Walk(w, h, layout, p, q):
  match c m:
    case False{} _:
      PF.both_absurd(PF.Walk(w, h, layout, p, q), B.at(Bool, False{}, s, q), hidq,
        %know_revealed(w, h, layout, s, f, T.Playing{}, q, onq) : {_ == True{} : Bool}; after)
    case True{} True{}:
      +s2 = B.set_at(Bool, s, p, True{})
      exact_explode(w, h, layout, s, p, q, hidq,
        %know_revealed(w, h, layout, s2, f, T.Lost{T.Exploded{p}}, q, onq) : {_ == True{} : Bool}; after,
        B.same(p, q), {==})
    case True{} False{}:
      +start = {[G.Work{p, Nil{}}] : List<&2, G.Work>}
      +cf = B.count_false(s)
      +hh = G.head_hidden(w, h, s, start)
      +fl = G.flood(cf, start, hh, w, h, layout, s)
      +st = G.won_or_playing(G.all_safe(w, h, layout, fl))
      PF.flood_path(cf, start, hh, w, h, layout, s, p, start_ok(w, h, layout, p), q, hidq,
        %know_revealed(w, h, layout, fl, f, st, q, onq) : {_ == True{} : Bool}; after)

law flood_exact_c:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for +s: T.Grid(Bool)
  for +f: List<&2, T.Pos>
  for +p: T.Pos
  for +q: T.Pos
  for before: {L.hidden(G.knowledge(G.Game{w, h, layout, s, f, T.Playing{}}), q) == True{} : Bool}
  for after: {L.revealed(G.knowledge(G.open(G.Game{w, h, layout, s, f, T.Playing{}}, p)), q) == True{} : Bool}
  PF.Walk(w, h, layout, p, q)

def flood_exact_c(w, h, layout, s, f, p, q, before, after):
  +u = {%PG.know_hidden(w, h, layout, s, f, T.Playing{}, q) : {_ == True{} : Bool};
    before : {G.unrevealed(w, h, s, q) == True{} : Bool}}
  flood_exact_c.go(w, h, layout, s, f, p, q, PF.unrev_on(w, h, s, q, u), PF.unrev_hidden(w, h, s, q, u),
    G.unrevealed(w, h, s, p), B.mine(layout, p), after)

# The opening laws for real games
# ===============================

def open_mine.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  shape: {L.shaped(Bool, w, h, layout) == True{} : Bool},
  +playing: {G.status(g) == T.Playing{} : T.Status}, +p: T.Pos, boom: {L.mine(layout, p) == True{} : Bool},
  c: Canon(w, h, layout, g)) ->
  {G.status(G.open(g, p)) == T.Lost{T.Exploded{p}} : T.Status} &
  {L.seen(G.knowledge(G.open(g, p)), p) == T.Boom{} : T.Seen}:
  match c:
    case (eg, facts):
      match facts:
        case (sh, f2):
          match f2:
            case (won, f3):
              match f3:
                case (cm, cl):
                  +s = shown_of(g)
                  +f = flags_of(g)
                  %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
                    {G.status(G.open(_, p)) == T.Lost{T.Exploded{p}} : T.Status} &
                    {L.seen(G.knowledge(G.open(_, p)), p) == T.Boom{} : T.Seen}
                  %Equal.sym(T.Status, G.status(g), T.Playing{}, playing) :
                    {G.status(G.open(G.Game{w, h, layout, s, f, _}, p)) == T.Lost{T.Exploded{p}} : T.Status} &
                    {L.seen(G.knowledge(G.open(G.Game{w, h, layout, s, f, _}, p)), p) == T.Boom{} : T.Seen}
                  open_mine_c(w, h, layout, s, f,
                    %Equal.sym(Bool, B.shaped(Bool, w, h, layout), L.shaped(Bool, w, h, layout), PC.shaped_eq(Bool, w, h, layout)) :
                      {_ == True{} : Bool}; shape,
                    sh,
                    %playing : {PI.calm(_, w, h, layout, s) == True{} : Bool}; cm,
                    p,
                    %Equal.sym(Bool, B.mine(layout, p), L.mine(layout, p), PC.mine_eq(layout, p)) :
                      {_ == True{} : Bool}; boom)

law open_mine_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for +p: T.Pos
  for boom: {L.mine(layout, p) == True{} : Bool}
  {G.status(G.open(g, p)) == T.Lost{T.Exploded{p}} : T.Status} &
  {L.seen(G.knowledge(G.open(g, p)), p) == T.Boom{} : T.Seen}

def open_mine_(w, h, layout, shape, g, r, playing, p, boom):
  open_mine.k(w, h, layout, g, shape, playing, p, boom, canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

def open_safe.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  +playing: {G.status(g) == T.Playing{} : T.Status}, +p: T.Pos, safe: {L.mine(layout, p) == False{} : Bool},
  c: Canon(w, h, layout, g)) ->
  {L.is_lost(G.status(G.open(g, p))) == False{} : Bool}:
  match c:
    case (eg, facts):
      +s = shown_of(g)
      +f = flags_of(g)
      %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
        {L.is_lost(G.status(G.open(_, p))) == False{} : Bool}
      %Equal.sym(T.Status, G.status(g), T.Playing{}, playing) :
        {L.is_lost(G.status(G.open(G.Game{w, h, layout, s, f, _}, p))) == False{} : Bool}
      open_safe_c(w, h, layout, s, f, p,
        %Equal.sym(Bool, B.mine(layout, p), L.mine(layout, p), PC.mine_eq(layout, p)) :
          {_ == False{} : Bool}; safe)

law open_safe_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for +p: T.Pos
  for safe: {L.mine(layout, p) == False{} : Bool}
  {L.is_lost(G.status(G.open(g, p))) == False{} : Bool}

def open_safe_(w, h, layout, shape, g, r, playing, p, safe):
  open_safe.k(w, h, layout, g, playing, p, safe, canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

def flood_complete.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  +playing: {G.status(g) == T.Playing{} : T.Status}, +p: T.Pos, +on: {L.on_board(w, h, p) == True{} : Bool},
  +q: T.Pos, +path: List<&2, T.Pos>, +wk: {L.zero_walk(path, w, h, layout, p, q) == True{} : Bool},
  c: Canon(w, h, layout, g)) ->
  {L.revealed(G.knowledge(G.open(g, p)), q) == True{} : Bool}:
  match c:
    case (eg, facts):
      match facts:
        case (sh, f2):
          match f2:
            case (won, f3):
              match f3:
                case (cm, cl):
                  +s = shown_of(g)
                  +f = flags_of(g)
                  %Equal.sym(G.Game, g, G.Game{w, h, layout, s, f, G.status(g)}, eg) :
                    {L.revealed(G.knowledge(G.open(_, p)), q) == True{} : Bool}
                  %Equal.sym(T.Status, G.status(g), T.Playing{}, playing) :
                    {L.revealed(G.knowledge(G.open(G.Game{w, h, layout, s, f, _}, p)), q) == True{} : Bool}
                  flood_complete_c(w, h, layout, s, f, sh, cl, p, on, q, path, wk)

law flood_complete_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for +p: T.Pos
  for +on: {L.on_board(w, h, p) == True{} : Bool}
  for +q: T.Pos
  for +path: List<&2, T.Pos>
  for +wk: {L.zero_walk(path, w, h, layout, p, q) == True{} : Bool}
  {L.revealed(G.knowledge(G.open(g, p)), q) == True{} : Bool}

def flood_complete_(w, h, layout, shape, g, r, playing, p, on, q, path, wk):
  flood_complete.k(w, h, layout, g, playing, p, on, q, path, wk, canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))

def flood_exact.k(+w: Nat, +h: Nat, +layout: T.Grid(Bool), +g: G.Game,
  +playing: {G.status(g) == T.Playing{} : T.Status}, +p: T.Pos, +q: T.Pos,
  before: {L.hidden(G.knowledge(g), q) == True{} : Bool},
  after: {L.revealed(G.knowledge(G.open(g, p)), q) == True{} : Bool},
  c: Canon(w, h, layout, g)) -> PF.Walk(w, h, layout, p, q):
  match c:
    case (+eg, facts):
      +s = shown_of(g)
      +f = flags_of(g)
      +gp = {G.Game{w, h, layout, s, f, T.Playing{}} : G.Game}
      flood_exact_c(w, h, layout, s, f, p, q,
        {%playing : {L.hidden(G.knowledge(G.Game{w, h, layout, s, f, _}), q) == True{} : Bool};
          %eg : {L.hidden(G.knowledge(_), q) == True{} : Bool};
          before : {L.hidden(G.knowledge(gp), q) == True{} : Bool}},
        {%playing : {L.revealed(G.knowledge(G.open(G.Game{w, h, layout, s, f, _}, p)), q) == True{} : Bool};
          %eg : {L.revealed(G.knowledge(G.open(_, p)), q) == True{} : Bool};
          after : {L.revealed(G.knowledge(G.open(gp, p)), q) == True{} : Bool}})

law flood_exact_:
  for +w: Nat
  for +h: Nat
  for +layout: T.Grid(Bool)
  for shape: {L.shaped(Bool, w, h, layout) == True{} : Bool}
  for +g: G.Game
  for r: L.Reachable(w, h, layout, g)
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for +p: T.Pos
  for +q: T.Pos
  for before: {L.hidden(G.knowledge(g), q) == True{} : Bool}
  for after: {L.revealed(G.knowledge(G.open(g, p)), q) == True{} : Bool}
  PF.Walk(w, h, layout, p, q)

def flood_exact_(w, h, layout, shape, g, r, playing, p, q, before, after):
  flood_exact.k(w, h, layout, g, playing, p, q, before, after, canon(w, h, layout, g, PI.inv_reach(w, h, layout, g, r)))
