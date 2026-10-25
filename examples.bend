import Base
import ./types.bend as T
import ./LAWS.bend as L

# Spec sanity checks: each def below holds by computation ({==}), so a wrong
# definition in LAWS.bend shows up here as a failed check.
#
# The board is 3x3 with one mine in the top-left corner:
#   * . .
#   . . .
#   . . .

def layout() -> T.Grid(Bool):
  [[True{}, False{}, False{}], [False{}, False{}, False{}], [False{}, False{}, False{}]]

def all_hidden(n: Nat) -> T.Knowledge:
  T.Knowledge{3n, 3n, n, [[T.Hidden{}, T.Hidden{}, T.Hidden{}], [T.Hidden{}, T.Hidden{}, T.Hidden{}], [T.Hidden{}, T.Hidden{}, T.Hidden{}]]}

# The centre shows 1 and the bottom-right corner shows c.
def opened(c: T.Seen) -> T.Knowledge:
  T.Knowledge{3n, 3n, 1n, [[T.Hidden{}, T.Hidden{}, T.Hidden{}], [T.Hidden{}, T.Shown{1n}, T.Hidden{}], [T.Hidden{}, T.Hidden{}, c]]}

def corner_has_3_neighbours() -> {List.length(&2, T.Pos, L.neighbours(3n, 3n, T.Pos{0n, 0n})) == 3n : Nat}:
  {==}

def edge_has_5_neighbours() -> {List.length(&2, T.Pos, L.neighbours(3n, 3n, T.Pos{1n, 0n})) == 5n : Nat}:
  {==}

def centre_has_8_neighbours() -> {List.length(&2, T.Pos, L.neighbours(3n, 3n, T.Pos{1n, 1n})) == 8n : Nat}:
  {==}

def centre_counts_1() -> {L.adj_mines(3n, 3n, layout(), T.Pos{1n, 1n}) == 1n : Nat}:
  {==}

def far_corner_counts_0() -> {L.adj_mines(3n, 3n, layout(), T.Pos{2n, 2n}) == 0n : Nat}:
  {==}

def edge_counts_1() -> {L.adj_mines(3n, 3n, layout(), T.Pos{1n, 0n}) == 1n : Nat}:
  {==}

def one_mine() -> {L.total_mines(layout()) == 1n : Nat}:
  {==}

def all_hidden_fits() -> {L.consistent(all_hidden(1n), layout()) == True{} : Bool}:
  {==}

def wrong_mine_count_misfits() -> {L.consistent(all_hidden(2n), layout()) == False{} : Bool}:
  {==}

def right_numbers_fit() -> {L.consistent(opened(T.Shown{0n}), layout()) == True{} : Bool}:
  {==}

def wrong_number_misfits() -> {L.consistent(opened(T.Shown{1n}), layout()) == False{} : Bool}:
  {==}

def boom_on_safe_misfits() -> {L.consistent(opened(T.Boom{}), layout()) == False{} : Bool}:
  {==}

def walk_from_zero() -> {L.zero_walk([T.Pos{1n, 1n}], 3n, 3n, layout(), T.Pos{2n, 2n}, T.Pos{1n, 1n}) == True{} : Bool}:
  {==}

def walk_stops_at_number() -> {L.zero_walk([T.Pos{1n, 1n}, T.Pos{0n, 0n}], 3n, 3n, layout(), T.Pos{2n, 2n}, T.Pos{0n, 0n}) == False{} : Bool}:
  {==}

def walk_needs_adjacency() -> {L.zero_walk([T.Pos{2n, 0n}], 3n, 3n, layout(), T.Pos{2n, 2n}, T.Pos{2n, 0n}) == False{} : Bool}:
  {==}

def walk_stays_on_board() -> {L.zero_walk([T.Pos{3n, 2n}], 3n, 3n, layout(), T.Pos{2n, 2n}, T.Pos{3n, 2n}) == False{} : Bool}:
  {==}

def shape_right() -> {L.shaped(Bool, 3n, 3n, layout()) == True{} : Bool}:
  {==}

def shape_wrong() -> {L.shaped(Bool, 2n, 3n, layout()) == False{} : Bool}:
  {==}

def not_all_revealed() -> {L.all_safe_revealed(opened(T.Shown{0n}), layout()) == False{} : Bool}:
  {==}

# Windows XP's custom limits.
def custom_in_range_kept() -> {L.custom(20n, 20n, 50n) == T.Setup{20n, 20n, 50n} : T.Setup}:
  {==}

def custom_too_big_clamped() -> {L.custom(100n, 3n, 5000n) == T.Setup{30n, 9n, 260n} : T.Setup}:
  {==}

def custom_mines_capped() -> {L.custom(9n, 9n, 999n) == T.Setup{9n, 9n, 71n} : T.Setup}:
  {==}

def custom_too_few_mines() -> {L.custom(9n, 9n, 0n) == T.Setup{9n, 9n, 10n} : T.Setup}:
  {==}
