import Base
import ./types.bend as T
import ./board.bend as B
import ./game.bend as G

# What the web page calls. Every rule lives in game.bend; these only pack and
# unpack values for JavaScript, which holds the game but never looks inside.

# The board for a level: width, height and mine count, clamped like Windows.
def level(l: T.Level) -> T.Setup:
  G.setup(l)

# The board before the first click, when no mines are placed yet.
def idle(+w: Nat, +h: Nat) -> T.Grid(T.Tile):
  G.display(G.fresh(w, h, B.blank(Bool, w, h, False{})))

# A game started by the first click at (x, y): mines are placed away from it
# using the random numbers rs, then the click is played.
def start(+w: Nat, +h: Nat, n: Nat, +x: Nat, +y: Nat, rs: List<&2, U32>) -> G.Game:
  +p = {T.Pos{x, y} : T.Pos}
  G.step(G.fresh(w, h, G.place_mines(w, h, n, p, rs)), T.Reveal{p})

def reveal(+g: G.Game, x: Nat, y: Nat) -> G.Game:
  G.step(g, T.Reveal{T.Pos{x, y}})

def chord(+g: G.Game, x: Nat, y: Nat) -> G.Game:
  G.step(g, T.Chord{T.Pos{x, y}})

def flag(+g: G.Game, x: Nat, y: Nat) -> G.Game:
  G.step(g, T.Flag{T.Pos{x, y}})

def assist(+g: G.Game) -> G.Game:
  G.step(g, T.Assist{})

# Every tile on screen, row by row.
def tiles(g: G.Game) -> T.Grid(T.Tile):
  G.display(g)

def status(g: G.Game) -> T.Status:
  G.status(g)

# How many flags count towards the mine counter (the ones on hidden cells).
def flags(g: G.Game) -> Nat:
  match g:
    case G.Game{+w, +h, layout, +shown, flags, status}:
      G.flags_shown(w, h, shown, flags)
