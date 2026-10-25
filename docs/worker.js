// Holds the game and passes the page's clicks to Bend (ui.mjs, built from
// ui.bend). The rules all live in Bend; this only converts lists and runs in a
// worker so a slow assist never freezes the page.
import UI from "./ui.mjs";

const arr = l => { const o = []; for (; l.$ === "Con"; l = l.tail) o.push(l.head); return o; };
const list = a => a.reduceRight((tail, head) => ({$: "Con", head, tail}), {$: "Nil"});
const code = t => t.$ === "Number" ? t.n : t.$;

let setup = null; // {w, h, mines}
let game = null;  // null until the first click

function view() {
  const tiles = game ? UI.tiles(game) : UI.idle(setup.w, setup.h);
  return {
    ...setup,
    started: game !== null,
    tiles: arr(tiles).map(r => arr(r).map(code)),
    status: game ? UI.status(game) : {$: "Playing"},
    flags: game ? UI.flags(game) : 0,
  };
}

onmessage = ({data: m}) => {
  const {w, h, mines} = setup || {};
  switch (m.op) {
    case "level": {
      const s = UI.level(m.level);
      setup = {w: s.w, h: s.h, mines: s.mines};
      game = null;
      break;
    }
    case "reset": game = null; break;
    case "reveal":
      if (game) game = UI.reveal(game, m.x, m.y);
      else game = UI.start(w, h, mines, m.x, m.y, list([...crypto.getRandomValues(new Uint32Array(w * h))]));
      break;
    case "chord": if (game) game = UI.chord(game, m.x, m.y); break;
    case "flag": if (game) game = UI.flag(game, m.x, m.y); break;
    case "assist": if (game) game = UI.assist(game); break;
  }
  postMessage({id: m.id, ...view()});
};
