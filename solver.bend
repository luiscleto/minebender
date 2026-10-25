import Base
import ./types.bend as T
import ./board.bend as B

# The no-guess solver: finds a provably safe hidden cell, or none.
#
# A hidden cell c is provably safe exactly when no layout consistent with
# what the player knows has a mine on c. For each hidden cell (row by row),
# the solver searches for such a layout with a mine on c; the first cell
# with none is the answer. A layout found also shows that every other cell
# it mines is not provably safe, which saves most searches.
#
# The search is a depth-first walk over the hidden cells, cells next to a
# number first. A partial layout gives each cell Some{mine} or None
# (unassigned). After each choice, the numbers around the cell and the
# total mine count are checked against what can still be reached; a full
# layout is checked for consistency before it counts.

# A revealed cell, and for a number, the cells it counts.
type Item is Data:
  Item{p: T.Pos, s: T.Seen, ns: List<&2, T.Pos>}

# A hidden cell to assign, and the numbers around it.
type Todo is Data:
  Todo{c: T.Pos, rel: List<&2, Item>}

type Ctx is Data:
  Ctx{w: Nat, h: Nat, n: Nat, rows: T.Grid(T.Seen), items: List<&2, Item>}

# Checking a full layout
# ----------------------

def items.put(s: T.Seen, +p: T.Pos, w: Nat, h: Nat, rest: List<&2, Item>) -> List<&2, Item>:
  match s:
    case T.Hidden{}:
      rest
    case T.Shown{k}:
      Item{p, T.Shown{k}, B.neighbours(w, h, p)} <> rest
    case T.Boom{}:
      Item{p, T.Boom{}, Nil{}} <> rest

# The revealed cells of ps.
def items(+w: Nat, +h: Nat, +rows: T.Grid(T.Seen), ps: List<&2, T.Pos>) -> List<&2, Item>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      items.put(B.at(T.Seen, T.Hidden{}, rows, p), p, w, h, items(w, h, rows, t))

def item_ok(s: T.Seen, +p: T.Pos, ns: List<&2, T.Pos>, +layout: T.Grid(Bool)) -> Bool:
  match s:
    case T.Hidden{}:
      True{}
    case T.Shown{k}:
      Bool.not(B.mine(layout, p)) && Nat.is_eq(B.count_mines(layout, ns), k)
    case T.Boom{}:
      B.mine(layout, p)

def items_ok(its: List<&2, Item>, +layout: T.Grid(Bool)) -> Bool:
  match its:
    case Nil{}:
      True{}
    case Item{p, s, ns} <> t:
      item_ok(s, p, ns, layout) && items_ok(t, layout)

# The layout is consistent with what the player knows.
def check(ctx: Ctx, +layout: T.Grid(Bool)) -> Bool:
  match ctx:
    case Ctx{+w, +h, n, rows, items}:
      B.shaped(Bool, w, h, layout) && B.shaped(T.Seen, w, h, rows)
        && Nat.is_eq(B.total_mines(layout), n) && items_ok(items, layout)

# Partial layouts
# ---------------

def start.cell(s: T.Seen) -> Maybe<&2, Bool>:
  match s:
    case T.Hidden{}:
      None{}
    case T.Shown{k}:
      Some{False{}}
    case T.Boom{}:
      Some{True{}}

def start.row(r: List<&2, T.Seen>) -> List<&2, Maybe<&2, Bool>>:
  match r:
    case Nil{}:
      Nil{}
    case s <> t:
      start.cell(s) <> start.row(t)

# What the revealed cells fix: no mine under a number, one under a Boom.
def start(rows: T.Grid(T.Seen)) -> T.Grid(Maybe<&2, Bool>):
  match rows:
    case Nil{}:
      Nil{}
    case r <> t:
      start.row(r) <> start(t)

def fill.row(r: List<&2, Maybe<&2, Bool>>) -> List<&2, Bool>:
  match r:
    case Nil{}:
      Nil{}
    case m <> t:
      Maybe.default(&2, Bool, m, False{}) <> fill.row(t)

def fill(part: T.Grid(Maybe<&2, Bool>)) -> T.Grid(Bool):
  match part:
    case Nil{}:
      Nil{}
    case r <> t:
      fill.row(r) <> fill(t)

def look(+part: T.Grid(Maybe<&2, Bool>), p: T.Pos) -> Maybe<&2, Bool>:
  B.at(Maybe<&2, Bool>, None{}, part, p)

def is_true(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case Some{b}:
      b
    case None{}:
      False{}

def is_none(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case Some{b}:
      False{}
    case None{}:
      True{}

def one_if(b: Bool) -> Nat:
  Bool.pick(Nat, b, 1n, 0n)

def row_true(r: List<&2, Maybe<&2, Bool>>) -> Nat:
  match r:
    case Nil{}:
      0n
    case m <> t:
      Nat.add(one_if(is_true(m)), row_true(t))

def row_none(r: List<&2, Maybe<&2, Bool>>) -> Nat:
  match r:
    case Nil{}:
      0n
    case +m <> t:
      Nat.add(one_if(is_none(m)), row_none(t))

def part_true(part: T.Grid(Maybe<&2, Bool>)) -> Nat:
  match part:
    case Nil{}:
      0n
    case r <> t:
      Nat.add(row_true(r), part_true(t))

def part_none(part: T.Grid(Maybe<&2, Bool>)) -> Nat:
  match part:
    case Nil{}:
      0n
    case r <> t:
      Nat.add(row_none(r), part_none(t))

def true_among(+part: T.Grid(Maybe<&2, Bool>), ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case q <> t:
      Nat.add(one_if(is_true(look(part, q))), true_among(part, t))

def none_among(+part: T.Grid(Maybe<&2, Bool>), ps: List<&2, T.Pos>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case q <> t:
      Nat.add(one_if(is_none(look(part, q))), none_among(part, t))

# Pruning
# -------

# k is still reachable from what is fixed: t mines, f unassigned cells.
def between(+t: Nat, +f: Nat, +k: Nat) -> Bool:
  Nat.is_le(t, k) && Nat.is_le(k, Nat.add(t, f))

def item_open(s: T.Seen, +part: T.Grid(Maybe<&2, Bool>), +ns: List<&2, T.Pos>) -> Bool:
  match s:
    case T.Shown{k}:
      between(true_among(part, ns), none_among(part, ns), k)
    case o:
      True{}

def items_open(+part: T.Grid(Maybe<&2, Bool>), its: List<&2, Item>) -> Bool:
  match its:
    case Nil{}:
      True{}
    case Item{p, s, ns} <> t:
      item_open(s, part, ns) && items_open(part, t)

# Some completion of the partial layout may still be consistent.
def open_ok(+part: T.Grid(Maybe<&2, Bool>), rel: List<&2, Item>, n: Nat) -> Bool:
  between(part_true(part), part_none(part), n) && items_open(part, rel)

# The search
# ----------

def ctx_n(ctx: Ctx) -> Nat:
  match ctx:
    case Ctx{w, h, n, rows, items}:
      n

def dfs.or(r: Maybe<&2, T.Grid(Bool)>, k: Unit -> Maybe<&2, T.Grid(Bool)>) ->
  Maybe<&2, T.Grid(Bool)>:
  match r:
    case None{}:
      k(Unit{})
    case Some{l}:
      Some{l}

def dfs.when(ok: Bool, k: Unit -> Maybe<&2, T.Grid(Bool)>) -> Maybe<&2, T.Grid(Bool)>:
  match ok:
    case False{}:
      None{}
    case True{}:
      k(Unit{})

def dfs.free(free: Bool, skip: Unit -> Maybe<&2, T.Grid(Bool)>,
  branch: Unit -> Maybe<&2, T.Grid(Bool)>) -> Maybe<&2, T.Grid(Bool)>:
  match free:
    case False{}:
      skip(Unit{})
    case True{}:
      branch(Unit{})

def leaf(+ctx: Ctx, +layout: T.Grid(Bool)) -> Maybe<&2, T.Grid(Bool)>:
  Bool.pick(Maybe<&2, T.Grid(Bool)>, check(ctx, layout), Some{layout}, None{})

# A consistent layout completing the partial one, assigning the cells of
# `todo` in order (cells already assigned are skipped).
def dfs(todo: List<&2, Todo>, +part: T.Grid(Maybe<&2, Bool>), +ctx: Ctx) ->
  Maybe<&2, T.Grid(Bool)>:
  match todo:
    case Nil{}:
      leaf(ctx, fill(part))
    case Todo{+c, +rel} <> +rest:
      +p0 = B.set_at(Maybe<&2, Bool>, part, c, Some{False{}})
      +p1 = B.set_at(Maybe<&2, Bool>, part, c, Some{True{}})
      +n = ctx_n(ctx)
      dfs.free(is_none(look(part, c)),
        u => dfs(rest, part, ctx),
        v => dfs.or(dfs.when(open_ok(p0, rel, n), x => dfs(rest, p0, ctx)),
          y => dfs.when(open_ok(p1, rel, n), z => dfs(rest, p1, ctx))))

# The cells of a solve
# --------------------

def is_hidden(s: T.Seen) -> Bool:
  match s:
    case T.Hidden{}:
      True{}
    case o:
      False{}

def hidden_cells(+rows: T.Grid(T.Seen), ps: List<&2, T.Pos>) -> List<&2, T.Pos>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      List.filter.put(T.Pos, p, hidden_cells(rows, t),
        is_hidden(B.at(T.Seen, T.Hidden{}, rows, p)))

def is_number(s: T.Seen) -> Bool:
  match s:
    case T.Shown{k}:
      True{}
    case o:
      False{}

def around.put(+i: Item, +c: T.Pos, rest: List<&2, Item>) -> List<&2, Item>:
  match i:
    case Item{p, s, ns}:
      List.filter.put(Item, i, rest, is_number(s) && B.contains(ns, c))

# The numbers of `is` that count c.
def around(its: List<&2, Item>, +c: T.Pos) -> List<&2, Item>:
  match its:
    case Nil{}:
      Nil{}
    case +i <> t:
      around.put(i, c, around(t, c))

def todos(+its: List<&2, Item>, cs: List<&2, T.Pos>) -> List<&2, Todo>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      Todo{c, around(its, c)} <> todos(its, t)

def has_rel(t: Todo) -> Bool:
  match t:
    case Todo{c, rel}:
      Bool.not(List.is_empty(&2, Item, rel))

# The cells next to a number.
def nears(ts: List<&2, Todo>) -> List<&2, Todo>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> rest:
      List.filter.put(Todo, t, nears(rest), has_rel(t))

# The other cells.
def fars(ts: List<&2, Todo>) -> List<&2, Todo>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> rest:
      List.filter.put(Todo, t, fars(rest), Bool.not(has_rel(t)))

# The cells next to a number first, then the rest.
def order(+ts: List<&2, Todo>) -> List<&2, Todo>:
  List.append(&2, Todo, nears(ts), fars(ts))

# The outer loop
# --------------

def covered(ls: List<&2, T.Grid(Bool)>, +c: T.Pos) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> t:
      B.mine(l, c) || covered(t, c)

def search(+c: T.Pos, todo: List<&2, Todo>, +part: T.Grid(Maybe<&2, Bool>), ctx: Ctx) ->
  Maybe<&2, T.Grid(Bool)>:
  dfs(todo, B.set_at(Maybe<&2, Bool>, part, c, Some{True{}}), ctx)

def loop.if(b: Bool, yes: Unit -> Maybe<&2, T.Pos>, no: Unit -> Maybe<&2, T.Pos>) ->
  Maybe<&2, T.Pos>:
  match b:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def loop.found(r: Maybe<&2, T.Grid(Bool)>, c: T.Pos,
  k: T.Grid(Bool) -> Maybe<&2, T.Pos>) -> Maybe<&2, T.Pos>:
  match r:
    case None{}:
      Some{c}
    case Some{l}:
      k(l)

# The first cell of hs that no consistent layout mines, given layouts
# `found` already shown consistent.
def loop(hs: List<&2, T.Pos>, +found: List<&2, T.Grid(Bool)>, +todo: List<&2, Todo>,
  +part: T.Grid(Maybe<&2, Bool>), +ctx: Ctx) -> Maybe<&2, T.Pos>:
  match hs:
    case Nil{}:
      None{}
    case +c <> +t:
      loop.if(covered(found, c),
        u => loop(t, found, todo, part, ctx),
        v => loop.found(search(c, todo, part, ctx), c,
          l => loop(t, l <> found, todo, part, ctx)))

def solve.go(ok: Bool, +hs: List<&2, T.Pos>, +w: Nat, +h: Nat, n: Nat,
  +rows: T.Grid(T.Seen)) -> Maybe<&2, T.Pos>:
  match ok:
    case False{}:
      List.head(&2, T.Pos, hs)
    case True{}:
      +its = items(w, h, rows, B.cells(w, h))
      loop(hs, Nil{}, order(todos(its, hs)), start(rows), Ctx{w, h, n, rows, its})

# A provably safe hidden cell, or None when every hidden cell might hold a
# mine.
def solve(k: T.Knowledge) -> Maybe<&2, T.Pos>:
  match k:
    case T.Knowledge{+w, +h, n, +rows}:
      solve.go(B.shaped(T.Seen, w, h, rows), hidden_cells(rows, B.cells(w, h)), w, h, n, rows)
