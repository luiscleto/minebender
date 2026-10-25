import Base
import ./types.bend as T
import ./board.bend as B
import ./solver.bend as S
import ./game.bend as G

# Self-play: reveal the solver's safe cell; when stuck, press the assist.
# A correct solver never loses.

type Run is Data:
  Run{g: G.Game, moves: Nat, assists: Nat}

def auto.pick(r: Maybe<&2, T.Pos>, g: G.Game, +moves: Nat, assists: Nat) -> Run:
  match r:
    case Some{p}:
      Run{G.step(g, T.Reveal{p}), 1n+moves, assists}
    case None{}:
      Run{G.step(g, T.Assist{moves}), 1n+moves, 1n+assists}

def auto.go(playing: Bool, +g: G.Game, moves: Nat, assists: Nat) -> Run:
  match playing:
    case False{}:
      Run{g, moves, assists}
    case True{}:
      auto.pick(S.solve(G.knowledge(g)), g, moves, assists)

def auto(fuel: Nat, r: Run) -> Run:
  match fuel:
    case 0n:
      r
    case 1n+f:
      match r:
        case Run{+g, moves, assists}:
          auto(f, auto.go(G.is_playing(G.status(g)), g, moves, assists))

def rng(n: Nat, +seed: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      +s = (seed * 1664525 + 1013904223 : U32)
      (s >> 8n : U32) <> rng(k, s)

def lost_str(l: T.Loss) -> String:
  match l:
    case T.Exploded{p}:
      "LOST (exploded)"
    case T.AssistTooEarly{p}:
      "LOST (assist too early)"

def status_str(s: T.Status) -> String:
  match s:
    case T.Playing{}:
      "playing"
    case T.Won{}:
      "WON"
    case T.Lost{why}:
      lost_str(why)

def report(r: Run) -> String:
  match r:
    case Run{g, moves, assists}:
      status_str(G.status(g)) ++ " moves=" ++ Nat.show(moves) ++ " assists=" ++ Nat.show(assists)

def game(+w: Nat, +h: Nat, n: Nat, +seed: U32) -> String:
  +first = {T.Pos{Nat.div(w, 2n), Nat.div(h, 2n)} : T.Pos}
  +layout = G.place_mines(w, h, n, first, rng(Nat.mul(w, h), seed))
  +g = G.step(G.fresh(w, h, layout), T.Reveal{first})
  report(auto(Nat.mul(w, h), Run{g, 0n, 0n}))

def auto_step(r: Maybe<&2, T.Pos>, g: G.Game) -> G.Game:
  match r:
    case Some{p}:
      G.step(g, T.Reveal{p})
    case None{}:
      G.step(g, T.Assist{0n})

def timed.go(fuel: Nat, +g: G.Game, playing: Bool) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      match playing:
        case False{}:
          IO.print(status_str(G.status(g)))
        case True{}:
          do IO<Unit>:
            t0 : Nat <- IO.now()
            +r : Maybe<&2, T.Pos> = S.solve(G.knowledge(g))
            t1 : Nat <- IO.now()
            IO.print(Nat.show(Nat.sub(t1, t0)) ++ "ms " ++ Bool.pick(String, Maybe.is_some(&2, T.Pos, r), "safe", "STUCK"))
            +g2 : G.Game = auto_step(r, g)
            timed.go(f, g2, G.is_playing(G.status(g2)))

def main() -> IO(Unit):
  +first = {T.Pos{15n, 8n} : T.Pos}
  +layout = G.place_mines(30n, 16n, 99n, first, rng(480n, 4))
  +g = G.step(G.fresh(30n, 16n, layout), T.Reveal{first})
  timed.go(480n, g, True{})
