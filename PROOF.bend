import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_grid.bend as PG
import ./proof_copy.bend as PC
import ./proof_gen.bend as PN
import ./proof_laws.bend as PW
import ./proof_assist.bend as PA
import ./proof_display.bend as PD

# Proofs of the laws in LAWS.bend: `def L.name` proves `law name`.

# Levels
# ======

def L.level_beginner():
  {==}

def L.level_intermediate():
  {==}

def L.level_expert():
  {==}

def L.level_custom(w, h, m):
  {==}

# Finished games
# ==============

def Bool.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def Bool.false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.disc(_)
  Unit{}

# In a finished game, opening a cell changes nothing.
law open_over:
  for +g: G.Game
  for +p: T.Pos
  for +over: {G.is_playing(G.status(g)) == False{} : Bool}
  {G.open(g, p) == g : G.Game}

def open_over(g, p, over):
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      %Equal.sym(Bool, G.is_playing(status), False{}, over) :
        {G.open.go(_ && G.unrevealed(w, h, shown, p), B.mine(layout, p),
          G.Game{w, h, layout, shown, flags, status}, p)
          == G.Game{w, h, layout, shown, flags, status} : G.Game}
      {==}

law not_playing:
  for +s: T.Status
  for ne: {s != T.Playing{} : T.Status}
  {G.is_playing(s) == False{} : Bool}

def not_playing(s, ne):
  match s:
    case T.Playing{}:
      Empty.absurd({G.is_playing(T.Playing{}) == False{} : Bool}, ne({==}))
    case T.Won{}:
      {==}
    case T.Lost{why}:
      {==}

law reveal_go_same:
  for +b: Bool
  for +g: G.Game
  for +p: T.Pos
  for +e: {G.open(g, p) == g : G.Game}
  {G.reveal.go(b, g, p) == g : G.Game}

def reveal_go_same(b, g, p, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

law reveal_over:
  for +g: G.Game
  for +p: T.Pos
  for +over: {G.is_playing(G.status(g)) == False{} : Bool}
  {G.reveal(g, p) == g : G.Game}

def reveal_over(g, p, over):
  reveal_go_same(G.flagged(g, p), g, p, open_over(g, p, over))

law chord_over:
  for +ts: List<&2, T.Pos>
  for +g: G.Game
  for +over: {G.is_playing(G.status(g)) == False{} : Bool}
  {G.chord_play(ts, g) == g : G.Game}

def chord_over(ts, g, over):
  match ts:
    case Nil{}:
      {==}
    case q <> t:
      %Equal.sym(G.Game, G.reveal(g, q), g, reveal_over(g, q, over)) :
        {G.chord_play(t, _) == g : G.Game}
      chord_over(t, g, over)

law flag_over:
  for +g: G.Game
  for +p: T.Pos
  for +over: {G.is_playing(G.status(g)) == False{} : Bool}
  {G.flag(g, p) == g : G.Game}

def flag_over(g, p, over):
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      %Equal.sym(Bool, G.is_playing(status), False{}, over) :
        {G.flag.go(_ && G.unrevealed(w, h, shown, p),
          G.Game{w, h, layout, shown, flags, status}, p)
          == G.Game{w, h, layout, shown, flags, status} : G.Game}
      {==}

law assist_over:
  for +g: G.Game
  for +over: {G.is_playing(G.status(g)) == False{} : Bool}
  for +k: Nat
  {G.assist(g, k) == g : G.Game}

def assist_over(g, over, k):
  %Equal.sym(Bool, G.is_playing(G.status(g)), False{}, over) :
    {G.assist.go(_, g, k) == g : G.Game}
  {==}

law frozen_:
  for +g: G.Game
  for over: {G.status(g) != T.Playing{} : T.Status}
  for a: T.Action
  {G.step(g, a) == g : G.Game}

def frozen_(g, over, a):
  match a:
    case T.Reveal{p}:
      reveal_over(g, p, not_playing(G.status(g), over))
    case T.Chord{p}:
      chord_over(G.chord_targets(g, p), g, not_playing(G.status(g), over))
    case T.Flag{p}:
      flag_over(g, p, not_playing(G.status(g), over))
    case T.Assist{k}:
      assist_over(g, not_playing(G.status(g), over), k)

def L.frozen(g, over, a):
  frozen_(g, over, a)

# Clicks
# ======

law reveal_flagged_:
  for +g: G.Game
  for +p: T.Pos
  for +flag: {G.flagged(g, p) == True{} : Bool}
  {G.step(g, T.Reveal{p}) == g : G.Game}

def reveal_flagged_(g, p, flag):
  %Equal.sym(Bool, G.flagged(g, p), True{}, flag) : {G.reveal.go(_, g, p) == g : G.Game}
  {==}

def L.reveal_flagged(g, p, flag):
  reveal_flagged_(g, p, flag)

law reveal_unflagged_:
  for +g: G.Game
  for +p: T.Pos
  for +flag: {G.flagged(g, p) == False{} : Bool}
  {G.step(g, T.Reveal{p}) == G.open(g, p) : G.Game}

def reveal_unflagged_(g, p, flag):
  %Equal.sym(Bool, G.flagged(g, p), False{}, flag) :
    {G.reveal.go(_, g, p) == G.open(g, p) : G.Game}
  {==}

def L.reveal_unflagged(g, p, flag):
  reveal_unflagged_(g, p, flag)

# Flags
# =====

def flag_k.go(+b: Bool, +g: G.Game, +p: T.Pos) ->
  {G.knowledge(G.flag.go(b, g, p)) == G.knowledge(g) : T.Knowledge}:
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case G.Game{w, h, layout, shown, flags, status}:
          {==}

def flag_s.go(+b: Bool, +g: G.Game, +p: T.Pos) ->
  {G.status(G.flag.go(b, g, p)) == G.status(g) : T.Status}:
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case G.Game{w, h, layout, shown, flags, status}:
          {==}

law flag_no_knowledge_:
  for +g: G.Game
  for +p: T.Pos
  {G.knowledge(G.step(g, T.Flag{p})) == G.knowledge(g) : T.Knowledge} &
  {G.status(G.step(g, T.Flag{p})) == G.status(g) : T.Status}

def flag_no_knowledge_(g, p):
  (flag_k.go(G.can_flag(g, p), g, p), flag_s.go(G.can_flag(g, p), g, p))

def L.flag_no_knowledge(g, p):
  flag_no_knowledge_(g, p)

def status_disc_playing(s: T.Status) -> Type:
  match s:
    case T.Playing{}:
      Empty
    case o:
      Unit

def won_ne_playing(e: {T.Won{} == T.Playing{} : T.Status}) -> Empty:
  %e : status_disc_playing(_)
  Unit{}

def lost_ne_playing(-why: T.Loss, e: {T.Lost{why} == T.Playing{} : T.Status}) -> Empty:
  %e : status_disc_playing(_)
  Unit{}

law flag_toggle_:
  for +g: G.Game
  for +playing: {G.status(g) == T.Playing{} : T.Status}
  for +p: T.Pos
  for +hid: {L.hidden(G.knowledge(g), p) == True{} : Bool}
  {G.flagged(G.step(g, T.Flag{p}), p) == Bool.not(G.flagged(g, p)) : Bool}

def flag_toggle_(g, playing, p, hid):
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      match status:
        case T.Playing{}:
          +gg = {G.Game{w, h, layout, shown, flags, T.Playing{}} : G.Game}
          +u = Equal.trans(Bool, G.unrevealed(w, h, shown, p),
            L.hidden(G.knowledge(gg), p), True{},
            Equal.sym(Bool, L.hidden(G.knowledge(gg), p), G.unrevealed(w, h, shown, p),
              PG.know_hidden(w, h, layout, shown, flags, T.Playing{}, p)), hid)
          %Equal.sym(Bool, G.unrevealed(w, h, shown, p), True{}, u) :
            {G.flagged(G.flag.go(_, gg, p), p) == Bool.not(G.flagged(gg, p)) : Bool}
          %Equal.sym(Bool, G.unrevealed(w, h, shown, p), True{}, u) :
            {Bool.and(_, B.contains(G.toggle(flags, p), p))
              == Bool.not(Bool.and(_, B.contains(flags, p))) : Bool}
          PG.toggle_self(flags, p)
        case T.Won{}:
          Empty.absurd({G.flagged(G.step(G.Game{w, h, layout, shown, flags, T.Won{}}, T.Flag{p}), p)
            == Bool.not(G.flagged(G.Game{w, h, layout, shown, flags, T.Won{}}, p)) : Bool},
            won_ne_playing(playing))
        case T.Lost{why}:
          Empty.absurd({G.flagged(G.step(G.Game{w, h, layout, shown, flags, T.Lost{why}}, T.Flag{p}), p)
            == Bool.not(G.flagged(G.Game{w, h, layout, shown, flags, T.Lost{why}}, p)) : Bool},
            lost_ne_playing(why, playing))

def L.flag_toggle(g, playing, p, hid):
  flag_toggle_(g, playing, p, hid)

def flag_others.go(+c: Bool, +g: G.Game, +p: T.Pos, +q: T.Pos,
  d: {B.same(p, q) == False{} : Bool}) ->
  {G.flagged(G.flag.go(c, g, p), q) == G.flagged(g, q) : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      match g:
        case G.Game{w, h, layout, shown, flags, status}:
          %Equal.sym(Bool, B.contains(G.toggle(flags, p), q), B.contains(flags, q),
            PG.toggle_other(flags, p, q, d)) :
            {Bool.and(G.unrevealed(w, h, shown, q), _)
              == Bool.and(G.unrevealed(w, h, shown, q), B.contains(flags, q)) : Bool}
          {==}

law flag_others_:
  for +g: G.Game
  for +p: T.Pos
  for +q: T.Pos
  for diff: {p != q : T.Pos}
  {G.flagged(G.step(g, T.Flag{p}), q) == G.flagged(g, q) : Bool}

def flag_others_(g, p, q, diff):
  flag_others.go(G.can_flag(g, p), g, p, q, PG.same_ne(p, q, diff))

def L.flag_others(g, p, q, diff):
  flag_others_(g, p, q, diff)

law flag_revealed_:
  for +g: G.Game
  for +p: T.Pos
  for +vis: {L.hidden(G.knowledge(g), p) == False{} : Bool}
  {G.step(g, T.Flag{p}) == g : G.Game}

def flag_revealed_(g, p, vis):
  match g:
    case G.Game{w, h, layout, shown, flags, status}:
      +gg = {G.Game{w, h, layout, shown, flags, status} : G.Game}
      +u = Equal.trans(Bool, G.unrevealed(w, h, shown, p),
        L.hidden(G.knowledge(gg), p), False{},
        Equal.sym(Bool, L.hidden(G.knowledge(gg), p), G.unrevealed(w, h, shown, p),
          PG.know_hidden(w, h, layout, shown, flags, status, p)), vis)
      %Equal.sym(Bool, G.unrevealed(w, h, shown, p), False{}, u) :
        {G.flag.go(Bool.and(G.is_playing(status), _), gg, p) == gg : G.Game}
      %Equal.sym(Bool, Bool.and(G.is_playing(status), False{}), False{},
        P.and_false_r(G.is_playing(status))) :
        {G.flag.go(_, gg, p) == gg : G.Game}
      {==}

def L.flag_revealed(g, p, vis):
  flag_revealed_(g, p, vis)

# Chording
# ========

law play_reveals:
  for +ts: List<&2, T.Pos>
  for +g: G.Game
  {G.chord_play(ts, g) == L.play(L.reveals(ts), g) : G.Game}

def play_reveals(ts, g):
  match ts:
    case Nil{}:
      {==}
    case q <> t:
      play_reveals(t, G.reveal(g, q))

law chord_:
  for +g: G.Game
  for +p: T.Pos
  {G.step(g, T.Chord{p}) == L.play(L.reveals(L.chord_targets(g, p)), g) : G.Game}

def chord_(g, p):
  %PC.chord_targets_eq(g, p) :
    {G.chord_play(G.chord_targets(g, p), g) == L.play(L.reveals(_), g) : G.Game}
  play_reveals(G.chord_targets(g, p), g)

def L.chord(g, p):
  chord_(g, p)

# Board generation
# ================

def L.gen_shape(w, h, n, first, rs):
  PN.gen_shape_(w, h, n, first, rs)

def L.gen_count(w, h, n, first, rs, on, fits):
  PN.gen_count_(w, h, n, first, rs, on, fits)

def L.gen_first_safe(w, h, n, first, rs):
  PN.gen_first_safe_(w, h, n, first, rs)

# The real board, winning and flags
# =================================

def L.bridge(w, h, layout, shape, g, r):
  PW.bridge_(w, h, layout, shape, g, r)

def L.won_iff(w, h, layout, shape, g, r):
  PW.won_iff_(w, h, layout, shape, g, r)

def L.flags_hidden(w, h, layout, shape, g, r, q, flag):
  PW.flags_hidden_(g, q, flag)

def L.monotone(w, h, layout, shape, g, r, a, q, vis):
  PW.monotone_(w, h, layout, shape, g, r, a, q, vis)

# Revealing
# =========

def L.open_mine(w, h, layout, shape, g, r, playing, p, boom):
  PW.open_mine_(w, h, layout, shape, g, r, playing, p, boom)

def L.open_safe(w, h, layout, shape, g, r, playing, p, safe):
  PW.open_safe_(w, h, layout, shape, g, r, playing, p, safe)

def L.flood_complete(w, h, layout, shape, g, r, playing, p, on, q, path, walk):
  PW.flood_complete_(w, h, layout, shape, g, r, playing, p, on, q, path, walk)

def L.flood_exact(w, h, layout, shape, g, r, playing, p, q, before, after):
  PW.flood_exact_(w, h, layout, shape, g, r, playing, p, q, before, after)

# The no-guess assist
# ===================

def L.assist_stuck(w, h, layout, shape, g, r, playing, stuck, k):
  PA.assist_stuck_(w, h, layout, shape, g, r, playing, stuck, k)

def L.assist_too_early(w, h, layout, shape, g, r, playing, q, option, k):
  PA.assist_too_early_(w, h, layout, shape, g, r, playing, q, option, k)

# The display
# ===========

def L.display_play(w, h, layout, shape, g, r, playing, p, on):
  PD.display_play_(w, h, layout, shape, g, r, playing, p, on)

def L.display_blast(w, h, layout, shape, g, r, p, lost, on):
  PD.display_blast_(w, h, layout, shape, g, r, p, lost, on)

def L.display_hint(w, h, layout, shape, g, r, s, lost, on):
  PD.display_hint_(w, h, layout, shape, g, r, s, lost, on)

def L.display_mines(w, h, layout, shape, g, r, over, q, on, m):
  PD.display_mines_(w, h, layout, shape, g, r, over, q, on, m)
