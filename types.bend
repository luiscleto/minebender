import Base

# The interface between the game and its laws. LAWS.bend talks about the game
# only through these types and the accessors in game.bend.

# A grid is a list of rows. A layout is a grid of Bool, True where a mine is.
def Grid(-A: Data) -> Data:
  List<&2, List<&2, A>>

# A cell: column x, row y; Pos{0n, 0n} is the top-left cell.
type Pos is Data:
  Pos{x: Nat, y: Nat}

# What the player sees in one cell. Flags are not here: they are the player's
# beliefs, not knowledge.
type Seen is Data:
  Hidden{}
  Shown{n: Nat}
  Boom{}

# Everything the player knows: the board is w columns by h rows, it holds
# `mines` mines in total, and `rows` holds one Seen per cell, row by row.
type Knowledge is Data:
  Knowledge{w: Nat, h: Nat, mines: Nat, rows: Grid(Seen)}

# What the player can do. The assist carries a random number, which picks
# the cell it opens when the player is stuck.
type Action is Data:
  Reveal{p: Pos}
  Chord{p: Pos}
  Flag{p: Pos}
  Assist{k: Nat}

# Why a game was lost: the player revealed the mine at p, or pressed the assist
# while `safe` could have been revealed without guessing.
type Loss is Data:
  Exploded{p: Pos}
  AssistTooEarly{safe: Pos}

type Status is Data:
  Playing{}
  Won{}
  Lost{why: Loss}

# A board size and mine count, as in Windows XP's Game menu.
type Level is Data:
  Beginner{}
  Intermediate{}
  Expert{}
  Custom{w: Nat, h: Nat, mines: Nat}

type Setup is Data:
  Setup{w: Nat, h: Nat, mines: Nat}

# What one cell looks like on screen.
type Tile is Data:
  Covered{}
  Flagged{}
  Number{n: Nat}
  Blast{}
  Mine{}
  BadFlag{}
  Hint{}
