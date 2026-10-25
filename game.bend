import Base
import ./types.bend as T

# STUB: signatures only, so that LAWS.bend type-checks while the laws are
# under review. Every body here is a placeholder.

type Game is Data:
  Game{w: Nat, h: Nat, layout: T.Grid(Bool), status: T.Status}

# A new game on a w-by-h board with the given mines, nothing revealed yet.
def fresh(w: Nat, h: Nat, layout: T.Grid(Bool)) -> Game:
  Game{w, h, layout, T.Playing{}}

def step(g: Game, a: T.Action) -> Game:
  g

# Reveal p whether or not it is flagged (Reveal, Chord and Assist use it).
def open(g: Game, p: T.Pos) -> Game:
  g

def knowledge(g: Game) -> T.Knowledge:
  match g:
    case Game{w, h, layout, status}:
      T.Knowledge{w, h, 0n, Nil{}}

def status(g: Game) -> T.Status:
  match g:
    case Game{w, h, layout, status}:
      status

def flagged(g: Game, p: T.Pos) -> Bool:
  False{}

# The board size and mine count a level plays with.
def setup(l: T.Level) -> T.Setup:
  T.Setup{9n, 9n, 10n}

# A w-by-h layout with n mines, none on `first`, shuffled by `rs`.
def place_mines(w: Nat, h: Nat, n: Nat, first: T.Pos, rs: List<&2, U32>) ->
  T.Grid(Bool):
  Nil{}
