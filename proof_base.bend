import Base

# Basic lemmas about Bool, Nat and List, used by PROOF.bend.

# Bool
# ====

def Bool.disc_ft(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law false_ne_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_ne_true(e):
  %e : Bool.disc_ft(_)
  Unit{}

law true_ne_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_ne_false(e):
  false_ne_true(Equal.sym(Bool, True{}, False{}, e))

law and_true_l:
  for +a: Bool
  for +b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_true_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(e))

law and_true_r:
  for +a: Bool
  for +b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_true_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(e))

law not_not:
  for +b: Bool
  {Bool.not(Bool.not(b)) == b : Bool}

def not_not(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Nat
# ===

def Nat.disc_z(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

law succ_ne_zero:
  for -n: Nat
  for e: {1n+n == 0n : Nat}
  Empty

def succ_ne_zero(n, e):
  %e : Nat.disc_z(_)
  Unit{}

law eq_refl:
  for +n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def eq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

law lt_irrefl:
  for +n: Nat
  {Nat.is_lt(n, n) == False{} : Bool}

def lt_irrefl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

law eq_sound:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def eq_sound(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, false_ne_true(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, false_ne_true(e))
    case 1n+p 1n+q:
      %eq_sound(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

law lt_zero:
  for +i: Nat
  {Nat.is_lt(i, 0n) == False{} : Bool}

def lt_zero(i):
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}

law sub_zero:
  for +i: Nat
  {Nat.sub(i, 0n) == i : Nat}

def sub_zero(i):
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}

law add_one:
  for +n: Nat
  {Nat.add(n, 1n) == 1n+n : Nat}

def add_one(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_one(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

law add_zero:
  for +n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def lt_succ.zero(+j: Nat, e: {Nat.is_lt(1n+j, 1n) == True{} : Bool}) -> Empty:
  false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{},
    Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, lt_zero(j)), e))

def lt_succ.lift(+j: Nat, +q: Nat,
  r: Or({Nat.is_lt(j, q) == True{} : Bool}, {j == q : Nat})) ->
  Or({Nat.is_lt(1n+j, 1n+q) == True{} : Bool}, {1n+j == 1n+q : Nat}):
  match r:
    case Inl{lt}:
      Inl{lt}
    case Inr{eq}:
      %eq : Or({Nat.is_lt(1n+j, 1n+q) == True{} : Bool}, {1n+j == 1n+_ : Nat})
      Inr{{==}}

# i < 1+p means i < p or i = p.
law lt_succ:
  for +i: Nat
  for +p: Nat
  for e: {Nat.is_lt(i, 1n+p) == True{} : Bool}
  Or({Nat.is_lt(i, p) == True{} : Bool}, {i == p : Nat})

def lt_succ(i, p, e):
  match i p:
    case 0n 0n:
      Inr{{==}}
    case 0n 1n+q:
      Inl{{==}}
    case 1n+j 0n:
      Empty.absurd(Or({Nat.is_lt(1n+j, 0n) == True{} : Bool}, {1n+j == 0n : Nat}),
        lt_succ.zero(j, e))
    case 1n+j 1n+q:
      lt_succ.lift(j, q, lt_succ(j, q, e))


# List
# ====

law append_nil:
  for -A: Data
  for +xs: List<&2, A>
  {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}

def append_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(A, t) : {h <> List.append(&2, A, t, Nil{}) == h <> _ : List<&2, A>}
      {==}

law append_assoc:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +zs: List<&2, A>
  {List.append(&2, A, List.append(&2, A, xs, ys), zs)
    == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}

def append_assoc(A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(A, t, ys, zs) :
        {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _ : List<&2, A>}
      {==}

law length_append:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  {List.length(&2, A, List.append(&2, A, xs, ys))
    == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}

def length_append(A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(A, t, ys) :
        {1n+List.length(&2, A, List.append(&2, A, t, ys)) == 1n+_ : Nat}
      {==}

# Before index length(xs), xs ++ ys reads like xs.
law get_append_l:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +i: Nat
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {List.get(&2, A, List.append(&2, A, xs, ys), i) == List.get(&2, A, xs, i) : Maybe<&2, A>}

def get_append_l(A, xs, ys, i, e):
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, A, ys, i) == None{} : Maybe<&2, A>},
        false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, lt_zero(i)), e)))
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      get_append_l(A, t, ys, k, e)

law get_append_len:
  for -A: Data
  for +xs: List<&2, A>
  for +v: A
  for +ys: List<&2, A>
  {List.get(&2, A, List.append(&2, A, xs, v <> ys), List.length(&2, A, xs)) == Some{v}
    : Maybe<&2, A>}

def get_append_len(A, xs, v, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      get_append_len(A, t, v, ys)

# Range
# =====

law range_acc:
  for +n: Nat
  for +acc: List<&2, Nat>
  {List.range.go(n, acc) == List.append(&2, Nat, List.range.go(n, Nil{}), acc) : List<&2, Nat>}

def range_acc(n, acc):
  match n:
    case 0n:
      {==}
    case 1n+p:
      +r = List.range.go(p, Nil{})
      %Equal.sym(List<&2, Nat>, List.range.go(p, [p]), List.append(&2, Nat, r, [p]),
        range_acc(p, [p])) :
        {List.range.go(p, p <> acc) == List.append(&2, Nat, _, acc) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, r, [p]), acc),
        List.append(&2, Nat, r, p <> acc), append_assoc(Nat, r, [p], acc)) :
        {List.range.go(p, p <> acc) == _ : List<&2, Nat>}
      range_acc(p, p <> acc)

law range_snoc:
  for +p: Nat
  {List.range(1n+p) == List.append(&2, Nat, List.range(p), [p]) : List<&2, Nat>}

def range_snoc(p):
  range_acc(p, [p])

law range_length:
  for +n: Nat
  {List.length(&2, Nat, List.range(n)) == n : Nat}

def range_length(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Nat>, List.range(1n+p), List.append(&2, Nat, List.range(p), [p]),
        range_snoc(p)) : {List.length(&2, Nat, _) == 1n+p : Nat}
      %Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, List.range(p), [p])),
        Nat.add(List.length(&2, Nat, List.range(p)), 1n), length_append(Nat, List.range(p), [p])) :
        {_ == 1n+p : Nat}
      %Equal.sym(Nat, List.length(&2, Nat, List.range(p)), p, range_length(p)) :
        {Nat.add(_, 1n) == 1n+p : Nat}
      add_one(p)

law range_get:
  for +n: Nat
  for +i: Nat
  for e: {Nat.is_lt(i, n) == True{} : Bool}
  {List.get(&2, Nat, List.range(n), i) == Some{i} : Maybe<&2, Nat>}

def range_get.cases(+p: Nat, +i: Nat,
  r: Or({Nat.is_lt(i, p) == True{} : Bool}, {i == p : Nat}),
  ih: {Nat.is_lt(i, p) == True{} : Bool} -> {List.get(&2, Nat, List.range(p), i) == Some{i} : Maybe<&2, Nat>}) ->
  {List.get(&2, Nat, List.append(&2, Nat, List.range(p), [p]), i) == Some{i} : Maybe<&2, Nat>}:
  match r:
    case Inl{+lt}:
      +lt2 = {%Equal.sym(Nat, List.length(&2, Nat, List.range(p)), p, range_length(p)) :
        {Nat.is_lt(i, _) == True{} : Bool}; lt : {Nat.is_lt(i, List.length(&2, Nat, List.range(p))) == True{} : Bool}}
      %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, List.append(&2, Nat, List.range(p), [p]), i),
        List.get(&2, Nat, List.range(p), i), get_append_l(Nat, List.range(p), [p], i, lt2)) :
        {_ == Some{i} : Maybe<&2, Nat>}
      ih(lt)
    case Inr{eq}:
      %Equal.sym(Nat, i, p, eq) :
        {List.get(&2, Nat, List.append(&2, Nat, List.range(p), [p]), _) == Some{_} : Maybe<&2, Nat>}
      %range_length(p) :
        {List.get(&2, Nat, List.append(&2, Nat, List.range(p), [p]), _) == Some{p} : Maybe<&2, Nat>}
      get_append_len(Nat, List.range(p), p, Nil{})

def range_get(n, i, e):
  match n:
    case 0n:
      Empty.absurd({List.get(&2, Nat, List.range(0n), i) == Some{i} : Maybe<&2, Nat>},
        false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, lt_zero(i)), e)))
    case 1n+p:
      %Equal.sym(List<&2, Nat>, List.range(1n+p), List.append(&2, Nat, List.range(p), [p]),
        range_snoc(p)) : {List.get(&2, Nat, _, i) == Some{i} : Maybe<&2, Nat>}
      range_get.cases(p, i, lt_succ(i, p, e), lt => range_get(p, i, lt))

law and_false_r:
  for +a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false_r(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law or_false_l:
  for +b: Bool
  {Bool.or(False{}, b) == b : Bool}

def or_false_l(b):
  {==}

# Past its end, a list has nothing.
law get_out:
  for -A: Data
  for +xs: List<&2, A>
  for +i: Nat
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == False{} : Bool}
  {List.get(&2, A, xs, i) == None{} : Maybe<&2, A>}

def get_out(A, xs, i, e):
  match xs i:
    case Nil{} _:
      {==}
    case h <> t 0n:
      Empty.absurd({List.get(&2, A, h <> t, 0n) == None{} : Maybe<&2, A>}, true_ne_false(e))
    case h <> t 1n+k:
      get_out(A, t, k, e)

law range_get_out:
  for +n: Nat
  for +i: Nat
  for e: {Nat.is_lt(i, n) == False{} : Bool}
  {List.get(&2, Nat, List.range(n), i) == None{} : Maybe<&2, Nat>}

def range_get_out(n, i, e):
  get_out(Nat, List.range(n), i,
    %Equal.sym(Nat, List.length(&2, Nat, List.range(n)), n, range_length(n)) :
      {Nat.is_lt(i, _) == False{} : Bool}; e)

# Arithmetic
# ==========

law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), add_comm(p, b)) :
        {1n+_ == Nat.add(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p))

law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

law add_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_left_comm(a, b, c):
  %add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), add_comm(a, b)) :
    {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  add_assoc(b, a, c)

law mul_zero_r:
  for +a: Nat
  {Nat.mul(a, 0n) == 0n : Nat}

def mul_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero_r(p)

law mul_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}

def mul_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +x = Nat.mul(p, b)
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, x), mul_succ_r(p, b)) :
        {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, x)) : Nat}
      %Equal.sym(Nat, Nat.add(b, Nat.add(p, x)), Nat.add(p, Nat.add(b, x)), add_left_comm(b, p, x)) :
        {1n+_ == 1n+Nat.add(p, Nat.add(b, x)) : Nat}
      {==}

law mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

def mul_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, mul_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, b), Nat.mul(b, p), mul_comm(p, b)) :
        {Nat.add(b, _) == Nat.mul(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), mul_succ_r(b, p))

law le_zero:
  for +n: Nat
  for e: {Nat.is_le(n, 0n) == True{} : Bool}
  {n == 0n : Nat}

def le_zero(n, e):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, false_ne_true(e))

law le_zero_l:
  for +n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}

def le_zero_l(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a <= b and a != b give a + 1 <= b.
law le_ne:
  for +a: Nat
  for +b: Nat
  for le: {Nat.is_le(a, b) == True{} : Bool}
  for ne: {Nat.is_eq(a, b) == False{} : Bool}
  {Nat.is_le(1n+a, b) == True{} : Bool}

def le_ne(a, b, le, ne):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, true_ne_false(ne))
    case 0n 1n+q:
      le_zero_l(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, false_ne_true(le))
    case 1n+p 1n+q:
      le_ne(p, q, le, ne)

# n < k + 1 gives n <= k.
law lt_succ_le:
  for +n: Nat
  for +k: Nat
  for e: {Nat.is_lt(n, 1n+k) == True{} : Bool}
  {Nat.is_le(n, k) == True{} : Bool}

def lt_succ_le(n, k, e):
  match n k:
    case 0n _:
      le_zero_l(k)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool},
        false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, lt_zero(p)), e)))
    case 1n+p 1n+q:
      lt_succ_le(p, q, e)

law or_false_inv:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_false_inv(a, b, e):
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(e))

law and_true_r_id:
  for +a: Bool
  {Bool.and(a, True{}) == a : Bool}

def and_true_r_id(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law not_true:
  for +b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_true(b, e):
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(e))

law not_false:
  for +b: Bool
  for e: {Bool.not(b) == False{} : Bool}
  {b == True{} : Bool}

def not_false(b, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, true_ne_false(e))

law succ_inj:
  for +a: Nat
  for +b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(a, b, e):
  Equal.cong(Nat, Nat, n => pred(n), 1n+a, 1n+b, e)

# Inequalities
# ============

law le_of_add:
  for +a: Nat
  for +k: Nat
  {Nat.is_le(a, Nat.add(a, k)) == True{} : Bool}

def le_of_add(a, k):
  match a:
    case 0n:
      le_zero_l(k)
    case 1n+p:
      le_of_add(p, k)

def LeW(+a: Nat, +b: Nat) -> Type:
  Exists(Nat, k => {b == Nat.add(a, k) : Nat})

def le_witness.lift(+p: Nat, +q: Nat, r: LeW(p, q)) -> LeW(1n+p, 1n+q):
  match r:
    case (k, e):
      (k, %Equal.sym(Nat, q, Nat.add(p, k), e) : {1n+_ == 1n+Nat.add(p, k) : Nat}; {==})

law le_witness:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == True{} : Bool}
  LeW(a, b)

def le_witness(a, b, e):
  match a b:
    case 0n _:
      (b, {==})
    case 1n+p 0n:
      Empty.absurd(LeW(1n+p, 0n), false_ne_true(e))
    case 1n+p 1n+q:
      le_witness.lift(p, q, le_witness(p, q, e))

law add_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def add_swap(a, b, c, d):
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), add_assoc(a, b, Nat.add(c, d))) :
    {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), add_assoc(a, c, Nat.add(b, d))) :
    {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %Equal.sym(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), add_left_comm(b, c, d)) :
    {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  {==}

def le_add.k(+a: Nat, +b: Nat, +c: Nat, +d: Nat, r1: LeW(a, b), r2: LeW(c, d)) ->
  {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  match r1:
    case (+k1, e1):
      match r2:
        case (+k2, e2):
          %Equal.sym(Nat, b, Nat.add(a, k1), e1) : {Nat.is_le(Nat.add(a, c), Nat.add(_, d)) == True{} : Bool}
          %Equal.sym(Nat, d, Nat.add(c, k2), e2) : {Nat.is_le(Nat.add(a, c), Nat.add(Nat.add(a, k1), _)) == True{} : Bool}
          %Equal.sym(Nat, Nat.add(Nat.add(a, k1), Nat.add(c, k2)), Nat.add(Nat.add(a, c), Nat.add(k1, k2)), add_swap(a, k1, c, k2)) :
            {Nat.is_le(Nat.add(a, c), _) == True{} : Bool}
          le_of_add(Nat.add(a, c), Nat.add(k1, k2))

law le_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for e1: {Nat.is_le(a, b) == True{} : Bool}
  for e2: {Nat.is_le(c, d) == True{} : Bool}
  {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}

def le_add(a, b, c, d, e1, e2):
  le_add.k(a, b, c, d, le_witness(a, b, e1), le_witness(c, d, e2))

law le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

def le_refl(a):
  %add_zero(a) : {Nat.is_le(a, _) == True{} : Bool}
  le_of_add(a, 0n)

law or_false_r:
  for +a: Bool
  {Bool.or(a, False{}) == a : Bool}

def or_false_r(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}
