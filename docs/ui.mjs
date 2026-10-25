function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= Number(w.head) << i;
    w = w.tail;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", head: ((x >>> i) & 1) === 1, tail: w};
  }
  return w;
}

function cmp_new(a, b) {
  return {$: a < b ? "LT" : a === b ? "EQ" : "GT"};
}

function nat_divmod(a, b) {
  return b === 0 ? {$: "Tuple", fst: 0, snd: a}
    : {$: "Tuple", fst: Math.trunc(a / b), snd: a % b};
}

function nat_chk(n) {
  if (n > 281474976710655) {
    throw "bend: a Nat past the largest immediate 2^48-1";
  }
  return n;
}

function nat_in(n) {
  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) {
    throw "bend: expected a Nat host number: an integer from 0 to 2^53";
  }
  return n;
}

function f32_show(x) {
  let s = "nan";
  for (let p = 1; x === x && p <= 9 && f32_round(s) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return (Object.is(x, -0) ? "-0" : s).replace("Infinity", "inf");
}

function f32_bits(x) {
  return new Uint32Array(new Float32Array([x]).buffer)[0];
}

function f32_from_bits(u) {
  return new Float32Array(new Uint32Array([u]).buffer)[0];
}

function f32_read(s) {
  const re = /^[\t\n\v\f\r ]*[+-]?((\d+(?:\.\d*)?|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  const v = f32_round(s.replace(/inf\w*/i, "Infinity"));
  return re.test(s) ? {$: "Some", value: v} : {$: "None"};
}

const f32_round = function f32_round(s) {
  const d = Number(s);
  const a = Math.abs(d);
  const f = Math.fround(a);
  const g = 2 * a - Math.min(f, 2 ** 128);
  if (g === f || Math.fround(g) !== g || g === Infinity) {
    return Math.sign(d) * f;
  }
  let k = 0;
  while (a * 2 ** k % 1 !== 0) {
    k += 1;
  }
  const [, i, r, e] = /(\d*)\.?(\d*)(?:e([+-]?\d+))?$/i.exec(s);
  const n = Number(e ?? 0) - r.length;
  const x = BigInt(i + r) * 2n ** BigInt(k) * 10n ** BigInt(Math.max(n, 0));
  const y = BigInt(a * 2 ** k) * 10n ** BigInt(Math.max(-n, 0));
  return Math.sign(d) * (x === y || x > y !== g > f ? f : g);
};

const char_new = function char_new(c) {
  return c < 55296 || c >= 57344 && c <= 1114111 ? String.fromCodePoint(c) : String.fromCharCode(56320, c >>> 22, c >>> 11 & 2047, c & 2047);
};

function char_len(s, at = 0) {
  return s[at] === "\uDC00" ? 4 : s.codePointAt(at) > 0xFFFF ? 2 : 1;
}

function char_code(s) {
  return s.length < 4 ? s.codePointAt(0)
    : (s.charCodeAt(1) << 22 | s.charCodeAt(2) << 11 | s.charCodeAt(3)) >>> 0;
}

function string_contains(s, p) {
  // A match must start at a Char boundary, not inside a packed U32 code.
  for (let at = 0; at <= s.length; at += char_len(s, at)) {
    if (s.startsWith(p, at)) {
      return true;
    }
  }
  return false;
}

function str_out(s) {
  return s.replace(/\uDC00[^]{3}/gu, "\uFFFD");
}

function str_in(s) {
  return s.replace(/\p{Cs}/gu, "\uFFFD");
}

// Array
// =====

function array_new(d, v) {
  if (d > 31) {
    throw "bend: an array past the deepest block class 31";
  }
  return Array(2 ** d).fill(v);
}

function array_node(a, b) {
  if (a.length !== b.length) {
    throw "bend: runtime fail-stop";
  }
  return a.concat(b);
}

function array_rmw(a, i, f) {
  const at = i % a.length;
  const old = a[at];
  a[at] = f(old);
  return {$: "Tuple", fst: a, snd: old};
}

// Run
// ===

function run_tail(f, x) {
  return {$: "$JMP", f: f.j?.f === f ? f.j : f, x};
}

function run_clo(j) {
  const f = (x) => run_loop(j(x));
  f.j = j;
  j.f = f;
  return f;
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(r.x);
  }
  return r;
}

function run_lib(f, n) {
  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)
    : run_loop(f(...a));
}

// Effect
// ======

const $0eff = Object.create(null);

function io_eff(k, run) {
  if (arguments.length > 2) {
    throw new Error("bend: " + k + " takes no need: an effect that waits parks itself");
  }
  if (k in $0eff) {
    throw new Error("bend: two effects register " + k);
  }
  $0eff[k] = run;
}
// Program
// =======

function $types_Grid() {
  return null;
}

function $board_at(_d_0, _g_0, _p_0) {
  const _x_0 = _p_0["x"];
  const _y_0 = _p_0["y"];
  const _row_0 = ($Maybe_default(($List_get(_g_0, _y_0)), {$: "Nil"}));
  return $Maybe_default(($List_get(_row_0, _x_0)), _d_0);
}

function $board_mine(_layout_0, _p_0) {
  return $board_at(false, _layout_0, _p_0);
}

function $board_on_board(_w_0, _h_0, _p_0) {
  const _x_0 = _p_0["x"];
  const _y_0 = _p_0["y"];
  return $Bool_and((_x_0 < _w_0), (_y_0 < _h_0));
}

function $board_same(_p_0, _q_0) {
  const _px_0 = _p_0["x"];
  const _py_0 = _p_0["y"];
  const _qx_0 = _q_0["x"];
  const _qy_0 = _q_0["y"];
  return $Bool_and(($Nat_is_eq(_px_0, _qx_0)), ($Nat_is_eq(_py_0, _qy_0)));
}

function $board_dist(_a_0, _b_0) {
  const _x_0 = (_a_0 < _b_0 ? 0 : _a_0 - _b_0);
  const _x_1 = (_b_0 < _a_0 ? 0 : _b_0 - _a_0);
  return nat_chk(_x_0 + _x_1);
}

function $board_within_one(_p_0, _q_0) {
  const _px_0 = _p_0["x"];
  const _py_0 = _p_0["y"];
  const _qx_0 = _q_0["x"];
  const _qy_0 = _q_0["y"];
  return $Bool_and(($Nat_is_le(($board_dist(_px_0, _qx_0)), 1)), ($Nat_is_le(($board_dist(_py_0, _qy_0)), 1)));
}

function $board_adjacent(_p_0, _q_0) {
  return $Bool_and(($Bool_not(($board_same(_p_0, _q_0)))), ($board_within_one(_p_0, _q_0)));
}

function $board_row_cells(_y_0, _xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _x_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": {$: "Pos", "x": _x_0, "y": _y_0}, "tail": ($board_row_cells(_y_0, _t_0))};
  }
}

function $board_cells_go(_w_0, _ys_0) {
  if (_ys_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _y_0 = _ys_0["head"];
    const _t_0 = _ys_0["tail"];
    return $List_append(($board_row_cells(_y_0, ($List_range(_w_0)))), ($board_cells_go(_w_0, _t_0)));
  }
}

function $board_cells(_w_0, _h_0) {
  return $board_cells_go(_w_0, ($List_range(_h_0)));
}

function $board_touching(_p_0, _qs_0) {
  if (_qs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _q_0 = _qs_0["head"];
    const _t_0 = _qs_0["tail"];
    return $List_filter_put(_q_0, ($board_touching(_p_0, _t_0)), ($board_adjacent(_p_0, _q_0)));
  }
}

function $board_neighbours(_w_0, _h_0, _p_0) {
  return $board_touching(_p_0, ($board_cells(_w_0, _h_0)));
}

function $board_count_mines(_layout_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _q_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    const _x_0 = ($Bool_pick(($board_mine(_layout_0, _q_0)), 1, 0));
    const _x_1 = ($board_count_mines(_layout_0, _t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $board_adj_mines(_w_0, _h_0, _layout_0, _p_0) {
  return $board_count_mines(_layout_0, ($board_neighbours(_w_0, _h_0, _p_0)));
}

function $board_row_mines(_row_0) {
  if (_row_0.$ === "Nil") {
    return 0;
  } else {
    const _b_0 = _row_0["head"];
    const _t_0 = _row_0["tail"];
    const _x_0 = ($Bool_pick(_b_0, 1, 0));
    const _x_1 = ($board_row_mines(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $board_total_mines(_layout_0) {
  if (_layout_0.$ === "Nil") {
    return 0;
  } else {
    const _r_0 = _layout_0["head"];
    const _t_0 = _layout_0["tail"];
    const _x_0 = ($board_row_mines(_r_0));
    const _x_1 = ($board_total_mines(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $board_zero(_w_0, _h_0, _layout_0, _p_0) {
  return $Bool_and(($Bool_and(($board_on_board(_w_0, _h_0, _p_0)), ($Bool_not(($board_mine(_layout_0, _p_0)))))), ($Nat_is_eq(($board_adj_mines(_w_0, _h_0, _layout_0, _p_0)), 0)));
}

function $board_rows_wide(_w_0, _g_0) {
  if (_g_0.$ === "Nil") {
    return true;
  } else {
    const _r_0 = _g_0["head"];
    const _t_0 = _g_0["tail"];
    return $Bool_and(($Nat_is_eq(($List_length(_r_0)), _w_0)), ($board_rows_wide(_w_0, _t_0)));
  }
}

function $board_shaped(_w_0, _h_0, _g_0) {
  return $Bool_and(($Nat_is_eq(($List_length(_g_0)), _h_0)), ($board_rows_wide(_w_0, _g_0)));
}

function $board_set_at(_g_0, _p_0, _v_0) {
  const _x_0 = _p_0["x"];
  const _y_0 = _p_0["y"];
  const _row_0 = ($Maybe_default(($List_get(_g_0, _y_0)), {$: "Nil"}));
  return $List_set(_g_0, _y_0, ($List_set(_row_0, _x_0, _v_0)));
}

function $board_blank(_w_0, _h_0, _v_0) {
  return $List_replicate(_h_0, ($List_replicate(_w_0, _v_0)));
}

function $board_row_false(_row_0) {
  if (_row_0.$ === "Nil") {
    return 0;
  } else {
    const _b_0 = _row_0["head"];
    const _t_0 = _row_0["tail"];
    const _x_0 = ($Bool_pick(_b_0, 0, 1));
    const _x_1 = ($board_row_false(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $board_count_false(_g_0) {
  if (_g_0.$ === "Nil") {
    return 0;
  } else {
    const _r_0 = _g_0["head"];
    const _t_0 = _g_0["tail"];
    const _x_0 = ($board_row_false(_r_0));
    const _x_1 = ($board_count_false(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $board_contains(_xs_0, _p_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _q_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = ($board_same(_q_0, _p_0));
    const _x_1 = ($board_contains(_t_0, _p_0));
    return (_x_0 || _x_1);
  }
}

function $board_remove(_xs_0, _p_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _q_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $List_filter_put(_q_0, ($board_remove(_t_0, _p_0)), ($Bool_not(($board_same(_q_0, _p_0)))));
  }
}

function $solver_items_put(_s_0, _p_0, _w_0, _h_0, _rest_0) {
  if (_s_0.$ === "Hidden") {
    return _rest_0;
  } else if (_s_0.$ === "Shown") {
    const _k_0 = _s_0["n"];
    return {$: "Con", "head": {$: "Item", "p": _p_0, "s": {$: "Shown", "n": _k_0}, "ns": ($board_neighbours(_w_0, _h_0, _p_0))}, "tail": _rest_0};
  } else {
    return {$: "Con", "head": {$: "Item", "p": _p_0, "s": {$: "Boom"}, "ns": {$: "Nil"}}, "tail": _rest_0};
  }
}

function $solver_items(_w_0, _h_0, _rows_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _p_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    return $solver_items_put(($board_at({$: "Hidden"}, _rows_0, _p_0)), _p_0, _w_0, _h_0, ($solver_items(_w_0, _h_0, _rows_0, _t_0)));
  }
}

function $solver_item_ok(_s_0, _p_0, _ns_0, _layout_0) {
  if (_s_0.$ === "Hidden") {
    return true;
  } else if (_s_0.$ === "Shown") {
    const _k_0 = _s_0["n"];
    return $Bool_and(($Bool_not(($board_mine(_layout_0, _p_0)))), ($Nat_is_eq(($board_count_mines(_layout_0, _ns_0)), _k_0)));
  } else {
    return $board_mine(_layout_0, _p_0);
  }
}

function $solver_items_ok(_its_0, _layout_0) {
  if (_its_0.$ === "Nil") {
    return true;
  } else {
    const _t_0 = _its_0["head"];
    const _p_0 = _t_0["p"];
    const _s_0 = _t_0["s"];
    const _ns_0 = _t_0["ns"];
    const _t_1 = _its_0["tail"];
    return $Bool_and(($solver_item_ok(_s_0, _p_0, _ns_0, _layout_0)), ($solver_items_ok(_t_1, _layout_0)));
  }
}

function $solver_check(_ctx_0, _layout_0) {
  const _w_0 = _ctx_0["w"];
  const _h_0 = _ctx_0["h"];
  const _n_0 = _ctx_0["n"];
  const _rows_0 = _ctx_0["rows"];
  const _items_0 = _ctx_0["items"];
  return $Bool_and(($Bool_and(($Bool_and(($board_shaped(_w_0, _h_0, _layout_0)), ($board_shaped(_w_0, _h_0, _rows_0)))), ($Nat_is_eq(($board_total_mines(_layout_0)), _n_0)))), ($solver_items_ok(_items_0, _layout_0)));
}

function $solver_start_cell(_s_0) {
  if (_s_0.$ === "Hidden") {
    return {$: "None"};
  } else if (_s_0.$ === "Shown") {
    return {$: "Some", "value": false};
  } else {
    return {$: "Some", "value": true};
  }
}

function $solver_start_row(_r_0) {
  if (_r_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _s_0 = _r_0["head"];
    const _t_0 = _r_0["tail"];
    return {$: "Con", "head": ($solver_start_cell(_s_0)), "tail": ($solver_start_row(_t_0))};
  }
}

function $solver_start(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _r_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    return {$: "Con", "head": ($solver_start_row(_r_0)), "tail": ($solver_start(_t_0))};
  }
}

function $solver_fill_row(_r_0) {
  if (_r_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _m_0 = _r_0["head"];
    const _t_0 = _r_0["tail"];
    return {$: "Con", "head": ($Maybe_default(_m_0, false)), "tail": ($solver_fill_row(_t_0))};
  }
}

function $solver_fill(_part_0) {
  if (_part_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _r_0 = _part_0["head"];
    const _t_0 = _part_0["tail"];
    return {$: "Con", "head": ($solver_fill_row(_r_0)), "tail": ($solver_fill(_t_0))};
  }
}

function $solver_look(_part_0, _p_0) {
  return $board_at({$: "None"}, _part_0, _p_0);
}

function $solver_is_true(_m_0) {
  if (_m_0.$ === "Some") {
    const _b_0 = _m_0["value"];
    return _b_0;
  } else {
    return false;
  }
}

function $solver_is_none(_m_0) {
  if (_m_0.$ === "Some") {
    return false;
  } else {
    return true;
  }
}

function $solver_one_if(_b_0) {
  return $Bool_pick(_b_0, 1, 0);
}

function $solver_row_true(_r_0) {
  if (_r_0.$ === "Nil") {
    return 0;
  } else {
    const _m_0 = _r_0["head"];
    const _t_0 = _r_0["tail"];
    const _x_0 = ($solver_one_if(($solver_is_true(_m_0))));
    const _x_1 = ($solver_row_true(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $solver_row_none(_r_0) {
  if (_r_0.$ === "Nil") {
    return 0;
  } else {
    const _m_0 = _r_0["head"];
    const _t_0 = _r_0["tail"];
    const _x_0 = ($solver_one_if(($solver_is_none(_m_0))));
    const _x_1 = ($solver_row_none(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $solver_part_true(_part_0) {
  if (_part_0.$ === "Nil") {
    return 0;
  } else {
    const _r_0 = _part_0["head"];
    const _t_0 = _part_0["tail"];
    const _x_0 = ($solver_row_true(_r_0));
    const _x_1 = ($solver_part_true(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $solver_part_none(_part_0) {
  if (_part_0.$ === "Nil") {
    return 0;
  } else {
    const _r_0 = _part_0["head"];
    const _t_0 = _part_0["tail"];
    const _x_0 = ($solver_row_none(_r_0));
    const _x_1 = ($solver_part_none(_t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $solver_true_among(_part_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _q_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    const _x_0 = ($solver_one_if(($solver_is_true(($solver_look(_part_0, _q_0))))));
    const _x_1 = ($solver_true_among(_part_0, _t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $solver_none_among(_part_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _q_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    const _x_0 = ($solver_one_if(($solver_is_none(($solver_look(_part_0, _q_0))))));
    const _x_1 = ($solver_none_among(_part_0, _t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $solver_between(_t_0, _f_0, _k_0) {
  return $Bool_and(($Nat_is_le(_t_0, _k_0)), ($Nat_is_le(_k_0, nat_chk(_t_0 + _f_0))));
}

function $solver_item_open(_s_0, _part_0, _ns_0) {
  if (_s_0.$ === "Shown") {
    const _k_0 = _s_0["n"];
    return $solver_between(($solver_true_among(_part_0, _ns_0)), ($solver_none_among(_part_0, _ns_0)), _k_0);
  } else {
    return true;
  }
}

function $solver_items_open(_part_0, _its_0) {
  if (_its_0.$ === "Nil") {
    return true;
  } else {
    const _t_0 = _its_0["head"];
    const _s_0 = _t_0["s"];
    const _ns_0 = _t_0["ns"];
    const _t_1 = _its_0["tail"];
    return $Bool_and(($solver_item_open(_s_0, _part_0, _ns_0)), ($solver_items_open(_part_0, _t_1)));
  }
}

function $solver_open_ok(_part_0, _rel_0, _n_0) {
  return $Bool_and(($solver_between(($solver_part_true(_part_0)), ($solver_part_none(_part_0)), _n_0)), ($solver_items_open(_part_0, _rel_0)));
}

function $solver_ctx_n(_ctx_0) {
  const _n_0 = _ctx_0["n"];
  return _n_0;
}

function $solver_dfs_or(_r_0, _k_0) {
  if (_r_0.$ === "None") {
    return run_tail(_k_0, {$: "Unit"});
  } else {
    const _l_0 = _r_0["value"];
    return {$: "Some", "value": _l_0};
  }
}

function $solver_dfs_when(_ok_0, _k_0) {
  if (!_ok_0) {
    return {$: "None"};
  } else {
    return run_tail(_k_0, {$: "Unit"});
  }
}

function $solver_dfs_free(_free_0, _skip_0, _branch_0) {
  if (!_free_0) {
    return run_tail(_skip_0, {$: "Unit"});
  } else {
    return run_tail(_branch_0, {$: "Unit"});
  }
}

function $solver_leaf(_ctx_0, _layout_0) {
  return $Bool_pick(($solver_check(_ctx_0, _layout_0)), {$: "Some", "value": _layout_0}, {$: "None"});
}

function $solver_dfs(_todo_0, _part_0, _ctx_0) {
  if (_todo_0.$ === "Nil") {
    return $solver_leaf(_ctx_0, ($solver_fill(_part_0)));
  } else {
    const _t_0 = _todo_0["head"];
    const _c_0 = _t_0["c"];
    const _rel_0 = _t_0["rel"];
    const _rest_0 = _todo_0["tail"];
    const _p0_0 = ($board_set_at(_part_0, _c_0, {$: "Some", "value": false}));
    const _p1_0 = ($board_set_at(_part_0, _c_0, {$: "Some", "value": true}));
    const _n_0 = ($solver_ctx_n(_ctx_0));
    return $solver_dfs_free(($solver_is_none(($solver_look(_part_0, _c_0)))), run_clo($solver_dfs_c1(_rest_0,_part_0,_ctx_0)), run_clo($solver_dfs_c2(_p0_0,_rel_0,_n_0,_rest_0,_ctx_0,_p1_0)));
  }
}

function $solver_dfs2(_todo_0, _part_0, _t_0, _f_0, _ctx_0) {
  if (_todo_0.$ === "Nil") {
    return $solver_leaf(_ctx_0, ($solver_fill(_part_0)));
  } else {
    const _t_1 = _todo_0["head"];
    const _c_0 = _t_1["c"];
    const _rel_0 = _t_1["rel"];
    const _rest_0 = _todo_0["tail"];
    const _p0_0 = ($board_set_at(_part_0, _c_0, {$: "Some", "value": false}));
    const _p1_0 = ($board_set_at(_part_0, _c_0, {$: "Some", "value": true}));
    const _n_0 = ($solver_ctx_n(_ctx_0));
    const _f1_0 = (_f_0 < 1 ? 0 : _f_0 - 1);
    return $solver_dfs_free(($solver_is_none(($solver_look(_part_0, _c_0)))), run_clo($solver_dfs2_c6(_rest_0,_part_0,_t_0,_f_0,_ctx_0)), run_clo($solver_dfs2_c7(_t_0,_f1_0,_n_0,_p0_0,_rel_0,_rest_0,_ctx_0,_p1_0)));
  }
}

function $solver_is_hidden(_s_0) {
  if (_s_0.$ === "Hidden") {
    return true;
  } else {
    return false;
  }
}

function $solver_hidden_cells(_rows_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _p_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    return $List_filter_put(_p_0, ($solver_hidden_cells(_rows_0, _t_0)), ($solver_is_hidden(($board_at({$: "Hidden"}, _rows_0, _p_0)))));
  }
}

function $solver_is_number(_s_0) {
  if (_s_0.$ === "Shown") {
    return true;
  } else {
    return false;
  }
}

function $solver_around_put(_i_0, _c_0, _rest_0) {
  const _p_0 = _i_0["p"];
  const _s_0 = _i_0["s"];
  const _ns_0 = _i_0["ns"];
  return $List_filter_put({$: "Item", "p": _p_0, "s": _s_0, "ns": _ns_0}, _rest_0, ($Bool_and(($solver_is_number(_s_0)), ($board_contains(_ns_0, _c_0)))));
}

function $solver_around(_its_0, _c_0) {
  if (_its_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _i_0 = _its_0["head"];
    const _t_0 = _its_0["tail"];
    return $solver_around_put(_i_0, _c_0, ($solver_around(_t_0, _c_0)));
  }
}

function $solver_todos(_its_0, _cs_0) {
  if (_cs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _c_0 = _cs_0["head"];
    const _t_0 = _cs_0["tail"];
    return {$: "Con", "head": {$: "Todo", "c": _c_0, "rel": ($solver_around(_its_0, _c_0))}, "tail": ($solver_todos(_its_0, _t_0))};
  }
}

function $solver_has_rel(_t_0) {
  const _rel_0 = _t_0["rel"];
  return $Bool_not(($List_is_empty(_rel_0)));
}

function $solver_nears(_ts_0) {
  if (_ts_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ts_0["head"];
    const _rest_0 = _ts_0["tail"];
    return $List_filter_put(_t_0, ($solver_nears(_rest_0)), ($solver_has_rel(_t_0)));
  }
}

function $solver_fars(_ts_0) {
  if (_ts_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ts_0["head"];
    const _rest_0 = _ts_0["tail"];
    return $List_filter_put(_t_0, ($solver_fars(_rest_0)), ($Bool_not(($solver_has_rel(_t_0)))));
  }
}

function $solver_order(_ts_0) {
  return $List_append(($solver_nears(_ts_0)), ($solver_fars(_ts_0)));
}

function $solver_todo_c(_t_0) {
  const _c_0 = _t_0["c"];
  return _c_0;
}

function $solver_rel_grid(_w_0, _h_0, _ts_0) {
  if (_ts_0.$ === "Nil") {
    return $board_blank(_w_0, _h_0, {$: "Nil"});
  } else {
    const _t_0 = _ts_0["head"];
    const _c_0 = _t_0["c"];
    const _rel_0 = _t_0["rel"];
    const _t_1 = _ts_0["tail"];
    return $board_set_at(($solver_rel_grid(_w_0, _h_0, _t_1)), _c_0, _rel_0);
  }
}

function $solver_reach_add_go(_fresh_0, _p_0, _queue_0, _order_0, _vis_0) {
  if (_fresh_0) {
    return {$: "Reach", "queue": ($List_append(_queue_0, {$: "Con", "head": _p_0, "tail": {$: "Nil"}})), "order": {$: "Con", "head": _p_0, "tail": _order_0}, "vis": ($board_set_at(_vis_0, _p_0, true))};
  } else {
    return {$: "Reach", "queue": _queue_0, "order": _order_0, "vis": _vis_0};
  }
}

function $solver_reach_add(_p_0, _relg_0, _r_0) {
  const _queue_0 = _r_0["queue"];
  const _order_0 = _r_0["order"];
  const _vis_0 = _r_0["vis"];
  return $solver_reach_add_go(($Bool_and(($Bool_not(($board_at(true, _vis_0, _p_0)))), ($Bool_not(($List_is_empty(($board_at({$: "Nil"}, _relg_0, _p_0)))))))), _p_0, _queue_0, _order_0, _vis_0);
}

function $solver_reach_ns($0, $1, $2) {
  for (;;) {
    {
      const _ns_0 = $0;
      const _relg_0 = $1;
      const _r_0 = $2;
      if (_ns_0.$ === "Nil") {
        return _r_0;
      } else {
        const _p_0 = _ns_0["head"];
        const _t_0 = _ns_0["tail"];
        $0 = _t_0;
        $1 = _relg_0;
        $2 = ($solver_reach_add(_p_0, _relg_0, _r_0));
        continue;
      }
    }
  }
}

function $solver_reach_items($0, $1, $2) {
  for (;;) {
    {
      const _rel_0 = $0;
      const _relg_0 = $1;
      const _r_0 = $2;
      if (_rel_0.$ === "Nil") {
        return _r_0;
      } else {
        const _t_0 = _rel_0["head"];
        const _ns_0 = _t_0["ns"];
        const _t_1 = _rel_0["tail"];
        $0 = _t_1;
        $1 = _relg_0;
        $2 = ($solver_reach_ns(_ns_0, _relg_0, _r_0));
        continue;
      }
    }
  }
}

function $solver_reach_run($0, $1, $2) {
  for (;;) {
    {
      const _fuel_0 = $0;
      const _relg_0 = $1;
      const _r_0 = $2;
      if (_fuel_0 === 0) {
        return _r_0;
      } else {
        const _f_0 = (_fuel_0 - 1);
        const _t_0 = _r_0["queue"];
        if (_t_0.$ === "Nil") {
          const _order_0 = _r_0["order"];
          const _vis_0 = _r_0["vis"];
          return {$: "Reach", "queue": {$: "Nil"}, "order": _order_0, "vis": _vis_0};
        } else {
          const _q_0 = _t_0["head"];
          const _rest_0 = _t_0["tail"];
          const _order_1 = _r_0["order"];
          const _vis_1 = _r_0["vis"];
          $0 = _f_0;
          $1 = _relg_0;
          $2 = ($solver_reach_items(($board_at({$: "Nil"}, _relg_0, _q_0)), _relg_0, {$: "Reach", "queue": _rest_0, "order": _order_1, "vis": _vis_1}));
          continue;
        }
      }
    }
  }
}

function $solver_reach_order(_r_0) {
  const _order_0 = _r_0["order"];
  return $List_reverse(_order_0);
}

function $solver_reach_start(_w_0, _h_0) {
  return {$: "Reach", "queue": {$: "Nil"}, "order": {$: "Nil"}, "vis": ($board_blank(_w_0, _h_0, false))};
}

function $solver_linked(_c_0, _w_0, _h_0, _fuel_0, _relg_0) {
  return $solver_reach_order(($solver_reach_run(_fuel_0, _relg_0, ($solver_reach_add(_c_0, _relg_0, ($solver_reach_start(_w_0, _h_0)))))));
}

function $solver_groups_go($0, $1, $2, $3) {
  for (;;) {
    {
      const _ts_0 = $0;
      const _fuel_0 = $1;
      const _relg_0 = $2;
      const _r_0 = $3;
      if (_ts_0.$ === "Nil") {
        return _r_0;
      } else {
        const _t_0 = _ts_0["head"];
        const _c_0 = _t_0["c"];
        const _t_1 = _ts_0["tail"];
        $0 = _t_1;
        $1 = _fuel_0;
        $2 = _relg_0;
        $3 = ($solver_reach_run(_fuel_0, _relg_0, ($solver_reach_add(_c_0, _relg_0, _r_0))));
        continue;
      }
    }
  }
}

function $solver_groups(_w_0, _h_0, _ts_0, _fuel_0, _relg_0) {
  return $solver_reach_order(($solver_groups_go(_ts_0, _fuel_0, _relg_0, ($solver_reach_start(_w_0, _h_0)))));
}

function $solver_with_c(_ts_0, _q_0) {
  if (_ts_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ts_0["head"];
    const _rest_0 = _ts_0["tail"];
    return $List_filter_put(_t_0, ($solver_with_c(_rest_0, _q_0)), ($board_same(($solver_todo_c(_t_0)), _q_0)));
  }
}

function $solver_gather(_qs_0, _ts_0) {
  if (_qs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _q_0 = _qs_0["head"];
    const _t_0 = _qs_0["tail"];
    return $List_append(($solver_with_c(_ts_0, _q_0)), ($solver_gather(_t_0, _ts_0)));
  }
}

function $solver_rot(_ts_0, _k_0) {
  return $List_append(($List_drop(_ts_0, _k_0)), ($List_take(_ts_0, _k_0)));
}

function $solver_spin(_c_0, _w_0, _n_0, _nf_0) {
  const _x_0 = _c_0["x"];
  const _y_0 = _c_0["y"];
  const _x_1 = nat_chk(_y_0 * _w_0);
  const _x_2 = nat_chk(_x_1 + _x_0);
  const _x_3 = nat_chk(_n_0 + 1);
  return $Nat_mod(nat_chk(_x_2 * _x_3), nat_chk(_nf_0 + 1));
}

function $solver_plan(_w_0, _h_0, _ts_0) {
  const _near_0 = ($solver_nears(_ts_0));
  const _far_0 = ($solver_fars(_ts_0));
  const _x_0 = ($List_length(_near_0));
  const _fuel_0 = nat_chk(_x_0 + 1);
  const _relg_0 = ($solver_rel_grid(_w_0, _h_0, _near_0));
  return {$: "Plan", "near": _near_0, "far": _far_0, "nf": ($List_length(_far_0)), "gq": ($solver_groups(_w_0, _h_0, _near_0, _fuel_0, _relg_0)), "base": ($solver_order(_ts_0)), "fuel": _fuel_0, "relg": _relg_0};
}

function $solver_plan_todo(_c_0, _pl_0, _ctx_0) {
  const _near_0 = _pl_0["near"];
  const _far_0 = _pl_0["far"];
  const _nf_0 = _pl_0["nf"];
  const _gq_0 = _pl_0["gq"];
  const _base_0 = _pl_0["base"];
  const _fuel_0 = _pl_0["fuel"];
  const _relg_0 = _pl_0["relg"];
  const _w_0 = _ctx_0["w"];
  const _h_0 = _ctx_0["h"];
  const _n_0 = _ctx_0["n"];
  return $List_append(($solver_gather(($List_append(($solver_linked(_c_0, _w_0, _h_0, _fuel_0, _relg_0)), _gq_0)), _near_0)), ($List_append(($solver_rot(_far_0, ($solver_spin(_c_0, _w_0, _n_0, _nf_0)))), _base_0)));
}

function $solver_covered(_ls_0, _c_0) {
  if (_ls_0.$ === "Nil") {
    return false;
  } else {
    const _l_0 = _ls_0["head"];
    const _t_0 = _ls_0["tail"];
    const _x_0 = ($board_mine(_l_0, _c_0));
    const _x_1 = ($solver_covered(_t_0, _c_0));
    return (_x_0 || _x_1);
  }
}

function $solver_search(_c_0, _pl_0, _part_0, _ctx_0) {
  const _p_0 = ($board_set_at(_part_0, _c_0, {$: "Some", "value": true}));
  return $solver_dfs2(($solver_plan_todo(_c_0, _pl_0, _ctx_0)), _p_0, ($solver_part_true(_p_0)), ($solver_part_none(_p_0)), _ctx_0);
}

function $solver_loop_if(_b_0, _yes_0, _no_0) {
  if (_b_0) {
    return run_tail(_yes_0, {$: "Unit"});
  } else {
    return run_tail(_no_0, {$: "Unit"});
  }
}

function $solver_loop_found(_r_0, _c_0, _k_0) {
  if (_r_0.$ === "None") {
    return {$: "Some", "value": _c_0};
  } else {
    const _l_0 = _r_0["value"];
    return run_tail(_k_0, _l_0);
  }
}

function $solver_loop(_hs_0, _found_0, _pl_0, _part_0, _ctx_0) {
  if (_hs_0.$ === "Nil") {
    return {$: "None"};
  } else {
    const _c_0 = _hs_0["head"];
    const _t_0 = _hs_0["tail"];
    return $solver_loop_if(($solver_covered(_found_0, _c_0)), run_clo($solver_loop_c11(_t_0,_found_0,_pl_0,_part_0,_ctx_0)), run_clo($solver_loop_c12(_c_0,_pl_0,_part_0,_ctx_0,_t_0,_found_0)));
  }
}

function $solver_solve_go(_ok_0, _hs_0, _w_0, _h_0, _n_0, _rows_0) {
  if (!_ok_0) {
    return $List_head(_hs_0);
  } else {
    const _its_0 = ($solver_items(_w_0, _h_0, _rows_0, ($board_cells(_w_0, _h_0))));
    return $solver_loop(_hs_0, {$: "Nil"}, ($solver_plan(_w_0, _h_0, ($solver_todos(_its_0, _hs_0)))), ($solver_start(_rows_0)), {$: "Ctx", "w": _w_0, "h": _h_0, "n": _n_0, "rows": _rows_0, "items": _its_0});
  }
}

function $solver_solve(_k_0) {
  const _w_0 = _k_0["w"];
  const _h_0 = _k_0["h"];
  const _n_0 = _k_0["mines"];
  const _rows_0 = _k_0["rows"];
  return $solver_solve_go(($board_shaped(_w_0, _h_0, _rows_0)), ($solver_hidden_cells(_rows_0, ($board_cells(_w_0, _h_0)))), _w_0, _h_0, _n_0, _rows_0);
}

function $game_status(_g_0) {
  const _status_0 = _g_0["status"];
  return _status_0;
}

function $game_is_playing(_s_0) {
  if (_s_0.$ === "Playing") {
    return true;
  } else {
    return false;
  }
}

function $game_unrevealed(_w_0, _h_0, _shown_0, _p_0) {
  return $Bool_and(($board_on_board(_w_0, _h_0, _p_0)), ($Bool_not(($board_at(false, _shown_0, _p_0)))));
}

function $game_flagged(_g_0, _p_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _shown_0 = _g_0["shown"];
  const _flags_0 = _g_0["flags"];
  return $Bool_and(($game_unrevealed(_w_0, _h_0, _shown_0, _p_0)), ($board_contains(_flags_0, _p_0)));
}

function $game_seen_pick(_s_0, _m_0, _w_0, _h_0, _layout_0, _p_0) {
  if (!_s_0) {
    return {$: "Hidden"};
  } else {
    if (_m_0) {
      return {$: "Boom"};
    } else {
      return {$: "Shown", "n": ($board_adj_mines(_w_0, _h_0, _layout_0, _p_0))};
    }
  }
}

function $game_seen_at(_w_0, _h_0, _layout_0, _shown_0, _p_0) {
  return $game_seen_pick(($board_at(false, _shown_0, _p_0)), ($board_mine(_layout_0, _p_0)), _w_0, _h_0, _layout_0, _p_0);
}

function $game_know_row(_w_0, _h_0, _layout_0, _shown_0, _y_0, _xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _x_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": ($game_seen_at(_w_0, _h_0, _layout_0, _shown_0, {$: "Pos", "x": _x_0, "y": _y_0})), "tail": ($game_know_row(_w_0, _h_0, _layout_0, _shown_0, _y_0, _t_0))};
  }
}

function $game_know_rows(_w_0, _h_0, _layout_0, _shown_0, _ys_0) {
  if (_ys_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _y_0 = _ys_0["head"];
    const _t_0 = _ys_0["tail"];
    return {$: "Con", "head": ($game_know_row(_w_0, _h_0, _layout_0, _shown_0, _y_0, ($List_range(_w_0)))), "tail": ($game_know_rows(_w_0, _h_0, _layout_0, _shown_0, _t_0))};
  }
}

function $game_knowledge(_g_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _layout_0 = _g_0["layout"];
  const _shown_0 = _g_0["shown"];
  return {$: "Knowledge", "w": _w_0, "h": _h_0, "mines": ($board_total_mines(_layout_0)), "rows": ($game_know_rows(_w_0, _h_0, _layout_0, _shown_0, ($List_range(_h_0))))};
}

function $game_all_safe_go(_layout_0, _shown_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return true;
  } else {
    const _p_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    const _x_0 = ($board_mine(_layout_0, _p_0));
    const _x_1 = ($board_at(false, _shown_0, _p_0));
    return $Bool_and((_x_0 || _x_1), ($game_all_safe_go(_layout_0, _shown_0, _t_0)));
  }
}

function $game_all_safe(_w_0, _h_0, _layout_0, _shown_0) {
  return $game_all_safe_go(_layout_0, _shown_0, ($board_cells(_w_0, _h_0)));
}

function $game_won_or_playing(_b_0) {
  if (_b_0) {
    return {$: "Won"};
  } else {
    return {$: "Playing"};
  }
}

function $game_fresh(_w_0, _h_0, _layout_0) {
  const _shown_0 = ($board_blank(_w_0, _h_0, false));
  return {$: "Game", "w": _w_0, "h": _h_0, "layout": _layout_0, "shown": _shown_0, "flags": {$: "Nil"}, "status": ($game_won_or_playing(($game_all_safe(_w_0, _h_0, _layout_0, _shown_0))))};
}

function $game_clamp(_lo_0, _hi_0, _x_0) {
  const _x_1 = (_hi_0 < _x_0 ? _hi_0 : _x_0);
  return (_lo_0 > _x_1 ? _lo_0 : _x_1);
}

function $game_custom(_w_0, _h_0, _m_0) {
  const _cw_0 = ($game_clamp(9, 30, _w_0));
  const _ch_0 = ($game_clamp(9, 25, _h_0));
  const _x_0 = nat_chk(_cw_0 * _ch_0);
  const _x_1 = ($game_clamp(10, 999, _m_0));
  const _x_2 = (_x_0 < 10 ? 0 : _x_0 - 10);
  return {$: "Setup", "w": _cw_0, "h": _ch_0, "mines": (_x_1 < _x_2 ? _x_1 : _x_2)};
}

function $game_setup(_l_0) {
  if (_l_0.$ === "Beginner") {
    return {$: "Setup", "w": 9, "h": 9, "mines": 10};
  } else if (_l_0.$ === "Intermediate") {
    return {$: "Setup", "w": 16, "h": 16, "mines": 40};
  } else if (_l_0.$ === "Expert") {
    return {$: "Setup", "w": 30, "h": 16, "mines": 99};
  } else {
    const _w_0 = _l_0["w"];
    const _h_0 = _l_0["h"];
    const _m_0 = _l_0["mines"];
    return $game_custom(_w_0, _h_0, _m_0);
  }
}

function $game_gen_coin(_r_0, _left_0, _need_0) {
  const _x_0 = ($Nat_mod(_r_0, _left_0));
  return (_x_0 < _need_0);
}

function $game_gen_pick(_need_0, _left_0, _rs_0) {
  if (_rs_0.$ === "Nil") {
    return $Nat_is_eq(_need_0, _left_0);
  } else {
    const _r_0 = _rs_0["head"];
    const _x_0 = ($Nat_is_eq(_need_0, _left_0));
    const _x_1 = ($game_gen_coin(_r_0, _left_0, _need_0));
    return (_x_0 || _x_1);
  }
}

function $game_gen_bit(_first_0, _p_0, _st_0) {
  const _need_0 = _st_0["need"];
  const _left_0 = _st_0["left"];
  const _rs_0 = _st_0["rs"];
  return $Bool_and(($Bool_and(($Bool_not(($board_same(_p_0, _first_0)))), (0 < _need_0))), ($game_gen_pick(_need_0, _left_0, _rs_0)));
}

function $game_gen_next_go(_skip_0, _bit_0, _need_0, _left_0, _rs_0) {
  if (_skip_0) {
    return {$: "GenState", "need": _need_0, "left": _left_0, "rs": _rs_0};
  } else {
    const _x_0 = ($Bool_pick(_bit_0, 1, 0));
    return {$: "GenState", "need": (_need_0 < _x_0 ? 0 : _need_0 - _x_0), "left": (_left_0 < 1 ? 0 : _left_0 - 1), "rs": ($List_tail(_rs_0))};
  }
}

function $game_gen_next(_first_0, _p_0, _st_0) {
  const _need_0 = _st_0["need"];
  const _left_0 = _st_0["left"];
  const _rs_0 = _st_0["rs"];
  return $game_gen_next_go(($board_same(_p_0, _first_0)), ($game_gen_bit(_first_0, _p_0, {$: "GenState", "need": _need_0, "left": _left_0, "rs": _rs_0})), _need_0, _left_0, _rs_0);
}

function $game_gen_row(_first_0, _y_0, _xs_0, _st_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _x_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _p_0 = {$: "Pos", "x": _x_0, "y": _y_0};
    return {$: "Con", "head": ($game_gen_bit(_first_0, _p_0, _st_0)), "tail": ($game_gen_row(_first_0, _y_0, _t_0, ($game_gen_next(_first_0, _p_0, _st_0))))};
  }
}

function $game_gen_row_state($0, $1, $2, $3) {
  for (;;) {
    {
      const _first_0 = $0;
      const _y_0 = $1;
      const _xs_0 = $2;
      const _st_0 = $3;
      if (_xs_0.$ === "Nil") {
        return _st_0;
      } else {
        const _x_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        $0 = _first_0;
        $1 = _y_0;
        $2 = _t_0;
        $3 = ($game_gen_next(_first_0, {$: "Pos", "x": _x_0, "y": _y_0}, _st_0));
        continue;
      }
    }
  }
}

function $game_gen_rows(_first_0, _w_0, _ys_0, _st_0) {
  if (_ys_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _y_0 = _ys_0["head"];
    const _t_0 = _ys_0["tail"];
    return {$: "Con", "head": ($game_gen_row(_first_0, _y_0, ($List_range(_w_0)), _st_0)), "tail": ($game_gen_rows(_first_0, _w_0, _t_0, ($game_gen_row_state(_first_0, _y_0, ($List_range(_w_0)), _st_0))))};
  }
}

function $game_gen_left(_first_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _p_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    const _x_0 = ($Bool_pick(($board_same(_p_0, _first_0)), 0, 1));
    const _x_1 = ($game_gen_left(_first_0, _t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $game_place_mines(_w_0, _h_0, _n_0, _first_0, _rs_0) {
  return $game_gen_rows(_first_0, _w_0, ($List_range(_h_0)), {$: "GenState", "need": _n_0, "left": ($game_gen_left(_first_0, ($board_cells(_w_0, _h_0)))), "rs": _rs_0});
}

function $game_head_hidden(_w_0, _h_0, _shown_0, _work_0) {
  if (_work_0.$ === "Nil") {
    return false;
  } else {
    const _t_0 = _work_0["head"];
    const _c_0 = _t_0["c"];
    return $game_unrevealed(_w_0, _h_0, _shown_0, _c_0);
  }
}

function $game_works(_ns_0, _back_0) {
  if (_ns_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _r_0 = _ns_0["head"];
    const _t_0 = _ns_0["tail"];
    return {$: "Con", "head": {$: "Work", "c": _r_0, "back": {$: "Con", "head": _r_0, "tail": _back_0}}, "tail": ($game_works(_t_0, _back_0))};
  }
}

function $game_push(_z_0, _ns_0, _back_0, _rest_0) {
  if (_z_0) {
    return $List_append(($game_works(_ns_0, _back_0)), _rest_0);
  } else {
    return _rest_0;
  }
}

function $game_flood($0, $1, $2, $3, $4, $5, $6) {
  for (;;) {
    {
      const _n_0 = $0;
      const _work_0 = $1;
      const _hd_0 = $2;
      const _w_0 = $3;
      const _h_0 = $4;
      const _layout_0 = $5;
      const _shown_0 = $6;
      if (_n_0 === 0) {
        return _shown_0;
      } else {
        const _m_0 = (_n_0 - 1);
        if (_work_0.$ === "Nil") {
          return _shown_0;
        } else {
          const _t_0 = _work_0["head"];
          const _c_0 = _t_0["c"];
          const _back_0 = _t_0["back"];
          const _rest_0 = _work_0["tail"];
          if (!_hd_0) {
            $0 = nat_chk(_m_0 + 1);
            $1 = _rest_0;
            $2 = ($game_head_hidden(_w_0, _h_0, _shown_0, _rest_0));
            $3 = _w_0;
            $4 = _h_0;
            $5 = _layout_0;
            $6 = _shown_0;
            continue;
          } else {
            const _sh_0 = ($board_set_at(_shown_0, _c_0, true));
            const _wk_0 = ($game_push(($board_zero(_w_0, _h_0, _layout_0, _c_0)), ($board_neighbours(_w_0, _h_0, _c_0)), _back_0, _rest_0));
            $0 = _m_0;
            $1 = _wk_0;
            $2 = ($game_head_hidden(_w_0, _h_0, _sh_0, _wk_0));
            $3 = _w_0;
            $4 = _h_0;
            $5 = _layout_0;
            $6 = _sh_0;
            continue;
          }
        }
      }
    }
  }
}

function $game_explode(_g_0, _p_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _layout_0 = _g_0["layout"];
  const _shown_0 = _g_0["shown"];
  const _flags_0 = _g_0["flags"];
  return {$: "Game", "w": _w_0, "h": _h_0, "layout": _layout_0, "shown": ($board_set_at(_shown_0, _p_0, true)), "flags": _flags_0, "status": {$: "Lost", "why": {$: "Exploded", "p": _p_0}}};
}

function $game_flood_open(_g_0, _p_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _layout_0 = _g_0["layout"];
  const _shown_0 = _g_0["shown"];
  const _flags_0 = _g_0["flags"];
  const _start_0 = {$: "Con", "head": {$: "Work", "c": _p_0, "back": {$: "Nil"}}, "tail": {$: "Nil"}};
  const _sh_0 = ($game_flood(($board_count_false(_shown_0)), _start_0, ($game_head_hidden(_w_0, _h_0, _shown_0, _start_0)), _w_0, _h_0, _layout_0, _shown_0));
  return {$: "Game", "w": _w_0, "h": _h_0, "layout": _layout_0, "shown": _sh_0, "flags": _flags_0, "status": ($game_won_or_playing(($game_all_safe(_w_0, _h_0, _layout_0, _sh_0))))};
}

function $game_open_go(_can_0, _boom_0, _g_0, _p_0) {
  if (!_can_0) {
    return _g_0;
  } else {
    if (_boom_0) {
      return $game_explode(_g_0, _p_0);
    } else {
      return $game_flood_open(_g_0, _p_0);
    }
  }
}

function $game_can_open(_g_0, _p_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _shown_0 = _g_0["shown"];
  const _status_0 = _g_0["status"];
  return $Bool_and(($game_is_playing(_status_0)), ($game_unrevealed(_w_0, _h_0, _shown_0, _p_0)));
}

function $game_layout_of(_g_0) {
  const _layout_0 = _g_0["layout"];
  return _layout_0;
}

function $game_open(_g_0, _p_0) {
  return $game_open_go(($game_can_open(_g_0, _p_0)), ($board_mine(($game_layout_of(_g_0)), _p_0)), _g_0, _p_0);
}

function $game_reveal_go(_f_0, _g_0, _p_0) {
  if (_f_0) {
    return _g_0;
  } else {
    return $game_open(_g_0, _p_0);
  }
}

function $game_reveal(_g_0, _p_0) {
  return $game_reveal_go(($game_flagged(_g_0, _p_0)), _g_0, _p_0);
}

function $game_flags_among(_g_0, _qs_0) {
  if (_qs_0.$ === "Nil") {
    return 0;
  } else {
    const _q_0 = _qs_0["head"];
    const _t_0 = _qs_0["tail"];
    const _x_0 = ($Bool_pick(($game_flagged(_g_0, _q_0)), 1, 0));
    const _x_1 = ($game_flags_among(_g_0, _t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $game_is_hidden(_s_0) {
  if (_s_0.$ === "Hidden") {
    return true;
  } else {
    return false;
  }
}

function $game_hidden(_v_0, _p_0) {
  const _w_0 = _v_0["w"];
  const _h_0 = _v_0["h"];
  const _rows_0 = _v_0["rows"];
  return $Bool_and(($board_on_board(_w_0, _h_0, _p_0)), ($game_is_hidden(($board_at({$: "Hidden"}, _rows_0, _p_0)))));
}

function $game_seen(_v_0, _p_0) {
  const _rows_0 = _v_0["rows"];
  return $board_at({$: "Hidden"}, _rows_0, _p_0);
}

function $game_hidden_unflagged(_g_0, _v_0, _qs_0) {
  if (_qs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _q_0 = _qs_0["head"];
    const _t_0 = _qs_0["tail"];
    return $List_filter_put(_q_0, ($game_hidden_unflagged(_g_0, _v_0, _t_0)), ($Bool_and(($game_hidden(_v_0, _q_0)), ($Bool_not(($game_flagged(_g_0, _q_0)))))));
  }
}

function $game_chord_targets_pick(_g_0, _v_0, _ns_0, _s_0) {
  if (_s_0.$ === "Shown") {
    const _k_0 = _s_0["n"];
    return $Bool_pick(($Nat_is_eq(($game_flags_among(_g_0, _ns_0)), _k_0)), ($game_hidden_unflagged(_g_0, _v_0, _ns_0)), {$: "Nil"});
  } else {
    return {$: "Nil"};
  }
}

function $game_chord_targets_go(_g_0, _v_0, _p_0) {
  const _w_0 = _v_0["w"];
  const _h_0 = _v_0["h"];
  const _n_0 = _v_0["mines"];
  const _rows_0 = _v_0["rows"];
  return $game_chord_targets_pick(_g_0, {$: "Knowledge", "w": _w_0, "h": _h_0, "mines": _n_0, "rows": _rows_0}, ($board_neighbours(_w_0, _h_0, _p_0)), ($game_seen({$: "Knowledge", "w": _w_0, "h": _h_0, "mines": _n_0, "rows": _rows_0}, _p_0)));
}

function $game_chord_targets(_g_0, _p_0) {
  return $game_chord_targets_go(_g_0, ($game_knowledge(_g_0)), _p_0);
}

function $game_chord_play($0, $1) {
  for (;;) {
    {
      const _ts_0 = $0;
      const _g_0 = $1;
      if (_ts_0.$ === "Nil") {
        return _g_0;
      } else {
        const _q_0 = _ts_0["head"];
        const _t_0 = _ts_0["tail"];
        $0 = _t_0;
        $1 = ($game_reveal(_g_0, _q_0));
        continue;
      }
    }
  }
}

function $game_toggle_go(_has_0, _flags_0, _p_0) {
  if (_has_0) {
    return $board_remove(_flags_0, _p_0);
  } else {
    return {$: "Con", "head": _p_0, "tail": _flags_0};
  }
}

function $game_toggle(_flags_0, _p_0) {
  return $game_toggle_go(($board_contains(_flags_0, _p_0)), _flags_0, _p_0);
}

function $game_flag_go(_c_0, _g_0, _p_0) {
  if (!_c_0) {
    return _g_0;
  } else {
    const _w_0 = _g_0["w"];
    const _h_0 = _g_0["h"];
    const _layout_0 = _g_0["layout"];
    const _shown_0 = _g_0["shown"];
    const _flags_0 = _g_0["flags"];
    const _status_0 = _g_0["status"];
    return {$: "Game", "w": _w_0, "h": _h_0, "layout": _layout_0, "shown": _shown_0, "flags": ($game_toggle(_flags_0, _p_0)), "status": _status_0};
  }
}

function $game_can_flag(_g_0, _p_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _shown_0 = _g_0["shown"];
  const _status_0 = _g_0["status"];
  return $Bool_and(($game_is_playing(_status_0)), ($game_unrevealed(_w_0, _h_0, _shown_0, _p_0)));
}

function $game_flag(_g_0, _p_0) {
  return $game_flag_go(($game_can_flag(_g_0, _p_0)), _g_0, _p_0);
}

function $game_safe_here(_layout_0, _shown_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return false;
  } else {
    const _p_0 = _ps_0["head"];
    return $Bool_and(($Bool_not(($board_mine(_layout_0, _p_0)))), ($Bool_not(($board_at(false, _shown_0, _p_0)))));
  }
}

function $game_first_safe_go($0, $1, $2, $3) {
  for (;;) {
    {
      const _ps_0 = $0;
      const _hit_0 = $1;
      const _layout_0 = $2;
      const _shown_0 = $3;
      if (_ps_0.$ === "Nil") {
        return {$: "None"};
      } else {
        const _p_0 = _ps_0["head"];
        const _t_0 = _ps_0["tail"];
        if (_hit_0) {
          return {$: "Some", "value": _p_0};
        } else {
          $0 = _t_0;
          $1 = ($game_safe_here(_layout_0, _shown_0, _t_0));
          $2 = _layout_0;
          $3 = _shown_0;
          continue;
        }
      }
    }
  }
}

function $game_first_safe(_layout_0, _shown_0, _ps_0) {
  return $game_first_safe_go(_ps_0, ($game_safe_here(_layout_0, _shown_0, _ps_0)), _layout_0, _shown_0);
}

function $game_safe_cell(_g_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _layout_0 = _g_0["layout"];
  const _shown_0 = _g_0["shown"];
  return $game_first_safe(_layout_0, _shown_0, ($board_cells(_w_0, _h_0)));
}

function $game_lose(_g_0, _p_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _layout_0 = _g_0["layout"];
  const _shown_0 = _g_0["shown"];
  const _flags_0 = _g_0["flags"];
  return {$: "Game", "w": _w_0, "h": _h_0, "layout": _layout_0, "shown": _shown_0, "flags": _flags_0, "status": {$: "Lost", "why": {$: "AssistTooEarly", "safe": _p_0}}};
}

function $game_assist_safe(_m_0, _g_0) {
  if (_m_0.$ === "None") {
    return _g_0;
  } else {
    const _p_0 = _m_0["value"];
    return $game_open(_g_0, _p_0);
  }
}

function $game_assist_pick(_r_0, _g_0) {
  if (_r_0.$ === "Some") {
    const _q_0 = _r_0["value"];
    return $game_lose(_g_0, _q_0);
  } else {
    return $game_assist_safe(($game_safe_cell(_g_0)), _g_0);
  }
}

function $game_assist_go(_playing_0, _g_0) {
  if (!_playing_0) {
    return _g_0;
  } else {
    return $game_assist_pick(run_loop($solver_solve(($game_knowledge(_g_0)))), _g_0);
  }
}

function $game_assist(_g_0) {
  return $game_assist_go(($game_is_playing(($game_status(_g_0)))), _g_0);
}

function $game_step(_g_0, _a_0) {
  if (_a_0.$ === "Reveal") {
    const _p_0 = _a_0["p"];
    return $game_reveal(_g_0, _p_0);
  } else if (_a_0.$ === "Chord") {
    const _p_1 = _a_0["p"];
    return $game_chord_play(($game_chord_targets(_g_0, _p_1)), _g_0);
  } else if (_a_0.$ === "Flag") {
    const _p_2 = _a_0["p"];
    return $game_flag(_g_0, _p_2);
  } else {
    return $game_assist(_g_0);
  }
}

function $game_mark_why(_why_0, _p_0) {
  if (_why_0.$ === "Exploded") {
    const _e_0 = _why_0["p"];
    return $Bool_pick(($board_same(_e_0, _p_0)), {$: "Some", "value": {$: "Blast"}}, {$: "None"});
  } else {
    const _s_0 = _why_0["safe"];
    return $Bool_pick(($board_same(_s_0, _p_0)), {$: "Some", "value": {$: "Hint"}}, {$: "None"});
  }
}

function $game_mark(_st_0, _p_0) {
  if (_st_0.$ === "Lost") {
    const _why_0 = _st_0["why"];
    return $game_mark_why(_why_0, _p_0);
  } else {
    return {$: "None"};
  }
}

function $game_tile_lost(_m_0, _f_0) {
  if (_m_0) {
    if (_f_0) {
      return {$: "Flagged"};
    } else {
      return {$: "Mine"};
    }
  } else {
    if (_f_0) {
      return {$: "BadFlag"};
    } else {
      return {$: "Covered"};
    }
  }
}

function $game_tile_hidden(_st_0, _m_0, _f_0) {
  if (_st_0.$ === "Playing") {
    return $Bool_pick(_f_0, {$: "Flagged"}, {$: "Covered"});
  } else if (_st_0.$ === "Won") {
    return $Bool_pick(_m_0, {$: "Flagged"}, {$: "Covered"});
  } else {
    return $game_tile_lost(_m_0, _f_0);
  }
}

function $game_tile_shown(_m_0, _w_0, _h_0, _layout_0, _p_0) {
  if (_m_0) {
    return {$: "Blast"};
  } else {
    return {$: "Number", "n": ($board_adj_mines(_w_0, _h_0, _layout_0, _p_0))};
  }
}

function $game_tile_go(_mk_0, _s_0, _m_0, _f_0, _st_0, _w_0, _h_0, _layout_0, _p_0) {
  if (_mk_0.$ === "Some") {
    const _t_0 = _mk_0["value"];
    return _t_0;
  } else {
    if (_s_0) {
      return $game_tile_shown(_m_0, _w_0, _h_0, _layout_0, _p_0);
    } else {
      return $game_tile_hidden(_st_0, _m_0, _f_0);
    }
  }
}

function $game_tile_at(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _st_0, _p_0) {
  return $game_tile_go(($game_mark(_st_0, _p_0)), ($board_at(false, _shown_0, _p_0)), ($board_mine(_layout_0, _p_0)), ($board_contains(_flags_0, _p_0)), _st_0, _w_0, _h_0, _layout_0, _p_0);
}

function $game_disp_row(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _st_0, _y_0, _xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _x_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": ($game_tile_at(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _st_0, {$: "Pos", "x": _x_0, "y": _y_0})), "tail": ($game_disp_row(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _st_0, _y_0, _t_0))};
  }
}

function $game_disp_rows(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _st_0, _ys_0) {
  if (_ys_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _y_0 = _ys_0["head"];
    const _t_0 = _ys_0["tail"];
    return {$: "Con", "head": ($game_disp_row(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _st_0, _y_0, ($List_range(_w_0)))), "tail": ($game_disp_rows(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _st_0, _t_0))};
  }
}

function $game_display(_g_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _layout_0 = _g_0["layout"];
  const _shown_0 = _g_0["shown"];
  const _flags_0 = _g_0["flags"];
  const _status_0 = _g_0["status"];
  return $game_disp_rows(_w_0, _h_0, _layout_0, _shown_0, _flags_0, _status_0, ($List_range(_h_0)));
}

function $game_flags_shown(_w_0, _h_0, _shown_0, _flags_0) {
  if (_flags_0.$ === "Nil") {
    return 0;
  } else {
    const _p_0 = _flags_0["head"];
    const _t_0 = _flags_0["tail"];
    const _x_0 = ($Bool_pick(($game_unrevealed(_w_0, _h_0, _shown_0, _p_0)), 1, 0));
    const _x_1 = ($game_flags_shown(_w_0, _h_0, _shown_0, _t_0));
    return nat_chk(_x_0 + _x_1);
  }
}

function $level(_l_0) {
  return $game_setup(_l_0);
}

function $idle(_w_0, _h_0) {
  return $game_display(($game_fresh(_w_0, _h_0, ($board_blank(_w_0, _h_0, false)))));
}

function $start(_w_0, _h_0, _n_0, _x_0, _y_0, _rs_0) {
  const _p_0 = {$: "Pos", "x": _x_0, "y": _y_0};
  return $game_step(($game_fresh(_w_0, _h_0, ($game_place_mines(_w_0, _h_0, _n_0, _p_0, _rs_0)))), {$: "Reveal", "p": _p_0});
}

function $reveal(_g_0, _x_0, _y_0) {
  return $game_step(_g_0, {$: "Reveal", "p": {$: "Pos", "x": _x_0, "y": _y_0}});
}

function $chord(_g_0, _x_0, _y_0) {
  return $game_step(_g_0, {$: "Chord", "p": {$: "Pos", "x": _x_0, "y": _y_0}});
}

function $flag(_g_0, _x_0, _y_0) {
  return $game_step(_g_0, {$: "Flag", "p": {$: "Pos", "x": _x_0, "y": _y_0}});
}

function $assist(_g_0) {
  return $game_step(_g_0, {$: "Assist"});
}

function $tiles(_g_0) {
  return $game_display(_g_0);
}

function $status(_g_0) {
  return $game_status(_g_0);
}

function $flags(_g_0) {
  const _w_0 = _g_0["w"];
  const _h_0 = _g_0["h"];
  const _shown_0 = _g_0["shown"];
  const _flags_0 = _g_0["flags"];
  return $game_flags_shown(_w_0, _h_0, _shown_0, _flags_0);
}

function $Maybe_default(_m_0, _d_0) {
  if (_m_0.$ === "None") {
    return _d_0;
  } else {
    const _x_0 = _m_0["value"];
    return _x_0;
  }
}

function $List_get($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      if (_xs_0.$ === "Nil") {
        return {$: "None"};
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        if (_n_0 === 0) {
          return {$: "Some", "value": _h_0};
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = _t_0;
          $1 = _p_0;
          continue;
        }
      }
    }
  }
}

function $Bool_and(_a_0, _b_0) {
  if (!_a_0) {
    return false;
  } else {
    return _b_0;
  }
}

function $Nat_is_eq(_a_0, _b_0) {
  return $Cmp_is_eq(cmp_new(_a_0, _b_0));
}

function $Nat_is_le(_a_0, _b_0) {
  return $Cmp_is_le(cmp_new(_a_0, _b_0));
}

function $Bool_not(_b_0) {
  if (!_b_0) {
    return true;
  } else {
    return false;
  }
}

function $List_append(_xs_0, _ys_0) {
  if (_xs_0.$ === "Nil") {
    return _ys_0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": _h_0, "tail": ($List_append(_t_0, _ys_0))};
  }
}

function $List_range(_n_0) {
  return $List_range_go(_n_0, {$: "Nil"});
}

function $List_filter_put(_h_0, _r_0, _keep_0) {
  if (!_keep_0) {
    return _r_0;
  } else {
    return {$: "Con", "head": _h_0, "tail": _r_0};
  }
}

function $Bool_pick(_c_0, _a_0, _b_0) {
  if (!_c_0) {
    return _b_0;
  } else {
    return _a_0;
  }
}

function $List_length(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _xs_0["tail"];
    return nat_chk(($List_length(_t_0)) + 1);
  }
}

function $List_set(_xs_0, _n_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    if (_n_0 === 0) {
      return {$: "Con", "head": _x_0, "tail": _t_0};
    } else {
      const _p_0 = (_n_0 - 1);
      return {$: "Con", "head": _h_0, "tail": ($List_set(_t_0, _p_0, _x_0))};
    }
  }
}

function $List_replicate(_n_0, _x_0) {
  if (_n_0 === 0) {
    return {$: "Nil"};
  } else {
    const _p_0 = (_n_0 - 1);
    return {$: "Con", "head": _x_0, "tail": ($List_replicate(_p_0, _x_0))};
  }
}

function $List_is_empty(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return true;
  } else {
    return false;
  }
}

function $List_reverse(_xs_0) {
  return $List_reverse_go(_xs_0, {$: "Nil"});
}

function $List_drop($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      if (_xs_0.$ === "Nil") {
        return {$: "Nil"};
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        if (_n_0 === 0) {
          return {$: "Con", "head": _h_0, "tail": _t_0};
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = _t_0;
          $1 = _p_0;
          continue;
        }
      }
    }
  }
}

function $List_take(_xs_0, _n_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    if (_n_0 === 0) {
      return {$: "Nil"};
    } else {
      const _p_0 = (_n_0 - 1);
      return {$: "Con", "head": _h_0, "tail": ($List_take(_t_0, _p_0))};
    }
  }
}

function $Nat_mod(_a_0, _b_0) {
  return $Pair_snd(nat_divmod(_a_0, _b_0));
}

function $List_head(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "None"};
  } else {
    const _h_0 = _xs_0["head"];
    return {$: "Some", "value": _h_0};
  }
}

function $List_tail(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _xs_0["tail"];
    return _t_0;
  }
}

function $Cmp_is_eq(_c_0) {
  if (_c_0.$ === "EQ") {
    return true;
  } else {
    return false;
  }
}

function $Cmp_is_le(_c_0) {
  if (_c_0.$ === "GT") {
    return false;
  } else {
    return true;
  }
}

function $List_range_go($0, $1) {
  for (;;) {
    {
      const _n_0 = $0;
      const _acc_0 = $1;
      if (_n_0 === 0) {
        return _acc_0;
      } else {
        const _p_0 = (_n_0 - 1);
        $0 = _p_0;
        $1 = {$: "Con", "head": _p_0, "tail": _acc_0};
        continue;
      }
    }
  }
}

function $List_reverse_go($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _acc_0 = $1;
      if (_xs_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        $0 = _t_0;
        $1 = {$: "Con", "head": _h_0, "tail": _acc_0};
        continue;
      }
    }
  }
}

function $Pair_snd(_p_0) {
  const _b_0 = _p_0["snd"];
  return _b_0;
}

function $solver_dfs_c1(_rest_0,_part_0,_ctx_0) {
  return (_x_0) => {
    return $solver_dfs(_rest_0, _part_0, _ctx_0);
  }
}
function $solver_dfs_c2(_p0_0,_rel_0,_n_0,_rest_0,_ctx_0,_p1_0) {
  return (_x_1) => {
    return $solver_dfs_or(run_loop($solver_dfs_when(($solver_open_ok(_p0_0, _rel_0, _n_0)), run_clo($solver_dfs_c3(_rest_0,_p0_0,_ctx_0)))), run_clo($solver_dfs_c4(_p1_0,_rel_0,_n_0,_rest_0,_ctx_0)));
  }
}
function $solver_dfs_c3(_rest_0,_p0_0,_ctx_0) {
  return (_x_2) => {
    return $solver_dfs(_rest_0, _p0_0, _ctx_0);
  }
}
function $solver_dfs_c4(_p1_0,_rel_0,_n_0,_rest_0,_ctx_0) {
  return (_x_3) => {
    return $solver_dfs_when(($solver_open_ok(_p1_0, _rel_0, _n_0)), run_clo($solver_dfs_c5(_rest_0,_p1_0,_ctx_0)));
  }
}
function $solver_dfs_c5(_rest_0,_p1_0,_ctx_0) {
  return (_x_4) => {
    return $solver_dfs(_rest_0, _p1_0, _ctx_0);
  }
}
function $solver_dfs2_c6(_rest_0,_part_0,_t_0,_f_0,_ctx_0) {
  return (_x_0) => {
    return $solver_dfs2(_rest_0, _part_0, _t_0, _f_0, _ctx_0);
  }
}
function $solver_dfs2_c7(_t_0,_f1_0,_n_0,_p0_0,_rel_0,_rest_0,_ctx_0,_p1_0) {
  return (_x_1) => {
    return $solver_dfs_or(run_loop($solver_dfs_when(($Bool_and(($solver_between(_t_0, _f1_0, _n_0)), ($solver_items_open(_p0_0, _rel_0)))), run_clo($solver_dfs2_c8(_rest_0,_p0_0,_t_0,_f1_0,_ctx_0)))), run_clo($solver_dfs2_c9(_t_0,_f1_0,_n_0,_p1_0,_rel_0,_rest_0,_ctx_0)));
  }
}
function $solver_dfs2_c8(_rest_0,_p0_0,_t_0,_f1_0,_ctx_0) {
  return (_x_2) => {
    return $solver_dfs2(_rest_0, _p0_0, _t_0, _f1_0, _ctx_0);
  }
}
function $solver_dfs2_c9(_t_0,_f1_0,_n_0,_p1_0,_rel_0,_rest_0,_ctx_0) {
  return (_x_3) => {
    return $solver_dfs_when(($Bool_and(($solver_between(nat_chk(_t_0 + 1), _f1_0, _n_0)), ($solver_items_open(_p1_0, _rel_0)))), run_clo($solver_dfs2_c10(_rest_0,_p1_0,_t_0,_f1_0,_ctx_0)));
  }
}
function $solver_dfs2_c10(_rest_0,_p1_0,_t_0,_f1_0,_ctx_0) {
  return (_x_4) => {
    return $solver_dfs2(_rest_0, _p1_0, nat_chk(_t_0 + 1), _f1_0, _ctx_0);
  }
}
function $solver_loop_c11(_t_0,_found_0,_pl_0,_part_0,_ctx_0) {
  return (_x_0) => {
    return $solver_loop(_t_0, _found_0, _pl_0, _part_0, _ctx_0);
  }
}
function $solver_loop_c12(_c_0,_pl_0,_part_0,_ctx_0,_t_0,_found_0) {
  return (_x_1) => {
    return $solver_loop_found(run_loop($solver_search(_c_0, _pl_0, _part_0, _ctx_0)), _c_0, run_clo($solver_loop_c13(_t_0,_found_0,_pl_0,_part_0,_ctx_0)));
  }
}
function $solver_loop_c13(_t_0,_found_0,_pl_0,_part_0,_ctx_0) {
  return (_x_2) => {
    return $solver_loop(_t_0, {$: "Con", "head": _x_2, "tail": _found_0}, _pl_0, _part_0, _ctx_0);
  }
}export default {
  "types:Grid": run_lib(() => run_loop($types_Grid()), 0),
  "board:at": run_lib((a0,a1,a2) => run_loop($board_at(a0,a1,a2)), 3),
  "board:mine": run_lib((a0,a1) => run_loop($board_mine(a0,a1)), 2),
  "board:on_board": run_lib((a0,a1,a2) => run_loop($board_on_board(nat_in(a0),nat_in(a1),a2)), 3),
  "board:same": run_lib((a0,a1) => run_loop($board_same(a0,a1)), 2),
  "board:dist": run_lib((a0,a1) => run_loop($board_dist(nat_in(a0),nat_in(a1))), 2),
  "board:within_one": run_lib((a0,a1) => run_loop($board_within_one(a0,a1)), 2),
  "board:adjacent": run_lib((a0,a1) => run_loop($board_adjacent(a0,a1)), 2),
  "board:row_cells": run_lib((a0,a1) => run_loop($board_row_cells(nat_in(a0),a1)), 2),
  "board:cells.go": run_lib((a0,a1) => run_loop($board_cells_go(nat_in(a0),a1)), 2),
  "board:cells": run_lib((a0,a1) => run_loop($board_cells(nat_in(a0),nat_in(a1))), 2),
  "board:touching": run_lib((a0,a1) => run_loop($board_touching(a0,a1)), 2),
  "board:neighbours": run_lib((a0,a1,a2) => run_loop($board_neighbours(nat_in(a0),nat_in(a1),a2)), 3),
  "board:count_mines": run_lib((a0,a1) => run_loop($board_count_mines(a0,a1)), 2),
  "board:adj_mines": run_lib((a0,a1,a2,a3) => run_loop($board_adj_mines(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "board:row_mines": run_lib((a0) => run_loop($board_row_mines(a0)), 1),
  "board:total_mines": run_lib((a0) => run_loop($board_total_mines(a0)), 1),
  "board:zero": run_lib((a0,a1,a2,a3) => run_loop($board_zero(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "board:rows_wide": run_lib((a0,a1) => run_loop($board_rows_wide(nat_in(a0),a1)), 2),
  "board:shaped": run_lib((a0,a1,a2) => run_loop($board_shaped(nat_in(a0),nat_in(a1),a2)), 3),
  "board:set_at": run_lib((a0,a1,a2) => run_loop($board_set_at(a0,a1,a2)), 3),
  "board:blank": run_lib((a0,a1,a2) => run_loop($board_blank(nat_in(a0),nat_in(a1),a2)), 3),
  "board:row_false": run_lib((a0) => run_loop($board_row_false(a0)), 1),
  "board:count_false": run_lib((a0) => run_loop($board_count_false(a0)), 1),
  "board:contains": run_lib((a0,a1) => run_loop($board_contains(a0,a1)), 2),
  "board:remove": run_lib((a0,a1) => run_loop($board_remove(a0,a1)), 2),
  "solver:items.put": run_lib((a0,a1,a2,a3,a4) => run_loop($solver_items_put(a0,a1,nat_in(a2),nat_in(a3),a4)), 5),
  "solver:items": run_lib((a0,a1,a2,a3) => run_loop($solver_items(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "solver:item_ok": run_lib((a0,a1,a2,a3) => run_loop($solver_item_ok(a0,a1,a2,a3)), 4),
  "solver:items_ok": run_lib((a0,a1) => run_loop($solver_items_ok(a0,a1)), 2),
  "solver:check": run_lib((a0,a1) => run_loop($solver_check(a0,a1)), 2),
  "solver:start.cell": run_lib((a0) => run_loop($solver_start_cell(a0)), 1),
  "solver:start.row": run_lib((a0) => run_loop($solver_start_row(a0)), 1),
  "solver:start": run_lib((a0) => run_loop($solver_start(a0)), 1),
  "solver:fill.row": run_lib((a0) => run_loop($solver_fill_row(a0)), 1),
  "solver:fill": run_lib((a0) => run_loop($solver_fill(a0)), 1),
  "solver:look": run_lib((a0,a1) => run_loop($solver_look(a0,a1)), 2),
  "solver:is_true": run_lib((a0) => run_loop($solver_is_true(a0)), 1),
  "solver:is_none": run_lib((a0) => run_loop($solver_is_none(a0)), 1),
  "solver:one_if": run_lib((a0) => run_loop($solver_one_if(a0)), 1),
  "solver:row_true": run_lib((a0) => run_loop($solver_row_true(a0)), 1),
  "solver:row_none": run_lib((a0) => run_loop($solver_row_none(a0)), 1),
  "solver:part_true": run_lib((a0) => run_loop($solver_part_true(a0)), 1),
  "solver:part_none": run_lib((a0) => run_loop($solver_part_none(a0)), 1),
  "solver:true_among": run_lib((a0,a1) => run_loop($solver_true_among(a0,a1)), 2),
  "solver:none_among": run_lib((a0,a1) => run_loop($solver_none_among(a0,a1)), 2),
  "solver:between": run_lib((a0,a1,a2) => run_loop($solver_between(nat_in(a0),nat_in(a1),nat_in(a2))), 3),
  "solver:item_open": run_lib((a0,a1,a2) => run_loop($solver_item_open(a0,a1,a2)), 3),
  "solver:items_open": run_lib((a0,a1) => run_loop($solver_items_open(a0,a1)), 2),
  "solver:open_ok": run_lib((a0,a1,a2) => run_loop($solver_open_ok(a0,a1,nat_in(a2))), 3),
  "solver:ctx_n": run_lib((a0) => run_loop($solver_ctx_n(a0)), 1),
  "solver:dfs.or": run_lib((a0,a1) => run_loop($solver_dfs_or(a0,a1)), 2),
  "solver:dfs.when": run_lib((a0,a1) => run_loop($solver_dfs_when(a0,a1)), 2),
  "solver:dfs.free": run_lib((a0,a1,a2) => run_loop($solver_dfs_free(a0,a1,a2)), 3),
  "solver:leaf": run_lib((a0,a1) => run_loop($solver_leaf(a0,a1)), 2),
  "solver:dfs": run_lib((a0,a1,a2) => run_loop($solver_dfs(a0,a1,a2)), 3),
  "solver:dfs2": run_lib((a0,a1,a2,a3,a4) => run_loop($solver_dfs2(a0,a1,nat_in(a2),nat_in(a3),a4)), 5),
  "solver:is_hidden": run_lib((a0) => run_loop($solver_is_hidden(a0)), 1),
  "solver:hidden_cells": run_lib((a0,a1) => run_loop($solver_hidden_cells(a0,a1)), 2),
  "solver:is_number": run_lib((a0) => run_loop($solver_is_number(a0)), 1),
  "solver:around.put": run_lib((a0,a1,a2) => run_loop($solver_around_put(a0,a1,a2)), 3),
  "solver:around": run_lib((a0,a1) => run_loop($solver_around(a0,a1)), 2),
  "solver:todos": run_lib((a0,a1) => run_loop($solver_todos(a0,a1)), 2),
  "solver:has_rel": run_lib((a0) => run_loop($solver_has_rel(a0)), 1),
  "solver:nears": run_lib((a0) => run_loop($solver_nears(a0)), 1),
  "solver:fars": run_lib((a0) => run_loop($solver_fars(a0)), 1),
  "solver:order": run_lib((a0) => run_loop($solver_order(a0)), 1),
  "solver:todo_c": run_lib((a0) => run_loop($solver_todo_c(a0)), 1),
  "solver:rel_grid": run_lib((a0,a1,a2) => run_loop($solver_rel_grid(nat_in(a0),nat_in(a1),a2)), 3),
  "solver:reach.add.go": run_lib((a0,a1,a2,a3,a4) => run_loop($solver_reach_add_go(a0,a1,a2,a3,a4)), 5),
  "solver:reach.add": run_lib((a0,a1,a2) => run_loop($solver_reach_add(a0,a1,a2)), 3),
  "solver:reach.ns": run_lib((a0,a1,a2) => run_loop($solver_reach_ns(a0,a1,a2)), 3),
  "solver:reach.items": run_lib((a0,a1,a2) => run_loop($solver_reach_items(a0,a1,a2)), 3),
  "solver:reach.run": run_lib((a0,a1,a2) => run_loop($solver_reach_run(nat_in(a0),a1,a2)), 3),
  "solver:reach.order": run_lib((a0) => run_loop($solver_reach_order(a0)), 1),
  "solver:reach.start": run_lib((a0,a1) => run_loop($solver_reach_start(nat_in(a0),nat_in(a1))), 2),
  "solver:linked": run_lib((a0,a1,a2,a3,a4) => run_loop($solver_linked(a0,nat_in(a1),nat_in(a2),nat_in(a3),a4)), 5),
  "solver:groups.go": run_lib((a0,a1,a2,a3) => run_loop($solver_groups_go(a0,nat_in(a1),a2,a3)), 4),
  "solver:groups": run_lib((a0,a1,a2,a3,a4) => run_loop($solver_groups(nat_in(a0),nat_in(a1),a2,nat_in(a3),a4)), 5),
  "solver:with_c": run_lib((a0,a1) => run_loop($solver_with_c(a0,a1)), 2),
  "solver:gather": run_lib((a0,a1) => run_loop($solver_gather(a0,a1)), 2),
  "solver:rot": run_lib((a0,a1) => run_loop($solver_rot(a0,nat_in(a1))), 2),
  "solver:spin": run_lib((a0,a1,a2,a3) => run_loop($solver_spin(a0,nat_in(a1),nat_in(a2),nat_in(a3))), 4),
  "solver:plan": run_lib((a0,a1,a2) => run_loop($solver_plan(nat_in(a0),nat_in(a1),a2)), 3),
  "solver:plan_todo": run_lib((a0,a1,a2) => run_loop($solver_plan_todo(a0,a1,a2)), 3),
  "solver:covered": run_lib((a0,a1) => run_loop($solver_covered(a0,a1)), 2),
  "solver:search": run_lib((a0,a1,a2,a3) => run_loop($solver_search(a0,a1,a2,a3)), 4),
  "solver:loop.if": run_lib((a0,a1,a2) => run_loop($solver_loop_if(a0,a1,a2)), 3),
  "solver:loop.found": run_lib((a0,a1,a2) => run_loop($solver_loop_found(a0,a1,a2)), 3),
  "solver:loop": run_lib((a0,a1,a2,a3,a4) => run_loop($solver_loop(a0,a1,a2,a3,a4)), 5),
  "solver:solve.go": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($solver_solve_go(a0,a1,nat_in(a2),nat_in(a3),nat_in(a4),a5)), 6),
  "solver:solve": run_lib((a0) => run_loop($solver_solve(a0)), 1),
  "game:status": run_lib((a0) => run_loop($game_status(a0)), 1),
  "game:is_playing": run_lib((a0) => run_loop($game_is_playing(a0)), 1),
  "game:unrevealed": run_lib((a0,a1,a2,a3) => run_loop($game_unrevealed(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "game:flagged": run_lib((a0,a1) => run_loop($game_flagged(a0,a1)), 2),
  "game:seen_pick": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($game_seen_pick(a0,a1,nat_in(a2),nat_in(a3),a4,a5)), 6),
  "game:seen_at": run_lib((a0,a1,a2,a3,a4) => run_loop($game_seen_at(nat_in(a0),nat_in(a1),a2,a3,a4)), 5),
  "game:know_row": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($game_know_row(nat_in(a0),nat_in(a1),a2,a3,nat_in(a4),a5)), 6),
  "game:know_rows": run_lib((a0,a1,a2,a3,a4) => run_loop($game_know_rows(nat_in(a0),nat_in(a1),a2,a3,a4)), 5),
  "game:knowledge": run_lib((a0) => run_loop($game_knowledge(a0)), 1),
  "game:all_safe.go": run_lib((a0,a1,a2) => run_loop($game_all_safe_go(a0,a1,a2)), 3),
  "game:all_safe": run_lib((a0,a1,a2,a3) => run_loop($game_all_safe(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "game:won_or_playing": run_lib((a0) => run_loop($game_won_or_playing(a0)), 1),
  "game:fresh": run_lib((a0,a1,a2) => run_loop($game_fresh(nat_in(a0),nat_in(a1),a2)), 3),
  "game:clamp": run_lib((a0,a1,a2) => run_loop($game_clamp(nat_in(a0),nat_in(a1),nat_in(a2))), 3),
  "game:custom": run_lib((a0,a1,a2) => run_loop($game_custom(nat_in(a0),nat_in(a1),nat_in(a2))), 3),
  "game:setup": run_lib((a0) => run_loop($game_setup(a0)), 1),
  "game:gen.coin": run_lib((a0,a1,a2) => run_loop($game_gen_coin(a0,nat_in(a1),nat_in(a2))), 3),
  "game:gen.pick": run_lib((a0,a1,a2) => run_loop($game_gen_pick(nat_in(a0),nat_in(a1),a2)), 3),
  "game:gen.bit": run_lib((a0,a1,a2) => run_loop($game_gen_bit(a0,a1,a2)), 3),
  "game:gen.next.go": run_lib((a0,a1,a2,a3,a4) => run_loop($game_gen_next_go(a0,a1,nat_in(a2),nat_in(a3),a4)), 5),
  "game:gen.next": run_lib((a0,a1,a2) => run_loop($game_gen_next(a0,a1,a2)), 3),
  "game:gen.row": run_lib((a0,a1,a2,a3) => run_loop($game_gen_row(a0,nat_in(a1),a2,a3)), 4),
  "game:gen.row_state": run_lib((a0,a1,a2,a3) => run_loop($game_gen_row_state(a0,nat_in(a1),a2,a3)), 4),
  "game:gen.rows": run_lib((a0,a1,a2,a3) => run_loop($game_gen_rows(a0,nat_in(a1),a2,a3)), 4),
  "game:gen.left": run_lib((a0,a1) => run_loop($game_gen_left(a0,a1)), 2),
  "game:place_mines": run_lib((a0,a1,a2,a3,a4) => run_loop($game_place_mines(nat_in(a0),nat_in(a1),nat_in(a2),a3,a4)), 5),
  "game:head_hidden": run_lib((a0,a1,a2,a3) => run_loop($game_head_hidden(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "game:works": run_lib((a0,a1) => run_loop($game_works(a0,a1)), 2),
  "game:push": run_lib((a0,a1,a2,a3) => run_loop($game_push(a0,a1,a2,a3)), 4),
  "game:flood": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($game_flood(nat_in(a0),a1,a2,nat_in(a3),nat_in(a4),a5,a6)), 7),
  "game:explode": run_lib((a0,a1) => run_loop($game_explode(a0,a1)), 2),
  "game:flood_open": run_lib((a0,a1) => run_loop($game_flood_open(a0,a1)), 2),
  "game:open.go": run_lib((a0,a1,a2,a3) => run_loop($game_open_go(a0,a1,a2,a3)), 4),
  "game:can_open": run_lib((a0,a1) => run_loop($game_can_open(a0,a1)), 2),
  "game:layout_of": run_lib((a0) => run_loop($game_layout_of(a0)), 1),
  "game:open": run_lib((a0,a1) => run_loop($game_open(a0,a1)), 2),
  "game:reveal.go": run_lib((a0,a1,a2) => run_loop($game_reveal_go(a0,a1,a2)), 3),
  "game:reveal": run_lib((a0,a1) => run_loop($game_reveal(a0,a1)), 2),
  "game:flags_among": run_lib((a0,a1) => run_loop($game_flags_among(a0,a1)), 2),
  "game:is_hidden": run_lib((a0) => run_loop($game_is_hidden(a0)), 1),
  "game:hidden": run_lib((a0,a1) => run_loop($game_hidden(a0,a1)), 2),
  "game:seen": run_lib((a0,a1) => run_loop($game_seen(a0,a1)), 2),
  "game:hidden_unflagged": run_lib((a0,a1,a2) => run_loop($game_hidden_unflagged(a0,a1,a2)), 3),
  "game:chord_targets.pick": run_lib((a0,a1,a2,a3) => run_loop($game_chord_targets_pick(a0,a1,a2,a3)), 4),
  "game:chord_targets.go": run_lib((a0,a1,a2) => run_loop($game_chord_targets_go(a0,a1,a2)), 3),
  "game:chord_targets": run_lib((a0,a1) => run_loop($game_chord_targets(a0,a1)), 2),
  "game:chord_play": run_lib((a0,a1) => run_loop($game_chord_play(a0,a1)), 2),
  "game:toggle.go": run_lib((a0,a1,a2) => run_loop($game_toggle_go(a0,a1,a2)), 3),
  "game:toggle": run_lib((a0,a1) => run_loop($game_toggle(a0,a1)), 2),
  "game:flag.go": run_lib((a0,a1,a2) => run_loop($game_flag_go(a0,a1,a2)), 3),
  "game:can_flag": run_lib((a0,a1) => run_loop($game_can_flag(a0,a1)), 2),
  "game:flag": run_lib((a0,a1) => run_loop($game_flag(a0,a1)), 2),
  "game:safe_here": run_lib((a0,a1,a2) => run_loop($game_safe_here(a0,a1,a2)), 3),
  "game:first_safe.go": run_lib((a0,a1,a2,a3) => run_loop($game_first_safe_go(a0,a1,a2,a3)), 4),
  "game:first_safe": run_lib((a0,a1,a2) => run_loop($game_first_safe(a0,a1,a2)), 3),
  "game:safe_cell": run_lib((a0) => run_loop($game_safe_cell(a0)), 1),
  "game:lose": run_lib((a0,a1) => run_loop($game_lose(a0,a1)), 2),
  "game:assist.safe": run_lib((a0,a1) => run_loop($game_assist_safe(a0,a1)), 2),
  "game:assist.pick": run_lib((a0,a1) => run_loop($game_assist_pick(a0,a1)), 2),
  "game:assist.go": run_lib((a0,a1) => run_loop($game_assist_go(a0,a1)), 2),
  "game:assist": run_lib((a0) => run_loop($game_assist(a0)), 1),
  "game:step": run_lib((a0,a1) => run_loop($game_step(a0,a1)), 2),
  "game:mark.why": run_lib((a0,a1) => run_loop($game_mark_why(a0,a1)), 2),
  "game:mark": run_lib((a0,a1) => run_loop($game_mark(a0,a1)), 2),
  "game:tile_lost": run_lib((a0,a1) => run_loop($game_tile_lost(a0,a1)), 2),
  "game:tile_hidden": run_lib((a0,a1,a2) => run_loop($game_tile_hidden(a0,a1,a2)), 3),
  "game:tile_shown": run_lib((a0,a1,a2,a3,a4) => run_loop($game_tile_shown(a0,nat_in(a1),nat_in(a2),a3,a4)), 5),
  "game:tile.go": run_lib((a0,a1,a2,a3,a4,a5,a6,a7,a8) => run_loop($game_tile_go(a0,a1,a2,a3,a4,nat_in(a5),nat_in(a6),a7,a8)), 9),
  "game:tile_at": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($game_tile_at(nat_in(a0),nat_in(a1),a2,a3,a4,a5,a6)), 7),
  "game:disp_row": run_lib((a0,a1,a2,a3,a4,a5,a6,a7) => run_loop($game_disp_row(nat_in(a0),nat_in(a1),a2,a3,a4,a5,nat_in(a6),a7)), 8),
  "game:disp_rows": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($game_disp_rows(nat_in(a0),nat_in(a1),a2,a3,a4,a5,a6)), 7),
  "game:display": run_lib((a0) => run_loop($game_display(a0)), 1),
  "game:flags_shown": run_lib((a0,a1,a2,a3) => run_loop($game_flags_shown(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "level": run_lib((a0) => run_loop($level(a0)), 1),
  "idle": run_lib((a0,a1) => run_loop($idle(nat_in(a0),nat_in(a1))), 2),
  "start": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($start(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4),a5)), 6),
  "reveal": run_lib((a0,a1,a2) => run_loop($reveal(a0,nat_in(a1),nat_in(a2))), 3),
  "chord": run_lib((a0,a1,a2) => run_loop($chord(a0,nat_in(a1),nat_in(a2))), 3),
  "flag": run_lib((a0,a1,a2) => run_loop($flag(a0,nat_in(a1),nat_in(a2))), 3),
  "assist": run_lib((a0) => run_loop($assist(a0)), 1),
  "tiles": run_lib((a0) => run_loop($tiles(a0)), 1),
  "status": run_lib((a0) => run_loop($status(a0)), 1),
  "flags": run_lib((a0) => run_loop($flags(a0)), 1),
};
