// Lean tab of the companion: for each result, a tree of boxes (the steps of its proof) holding the Lean declarations,
// with folding, zoom (buttons, Ctrl + wheel, pinch), panning, arrows to the declarations that the selected one uses,
// and a panel with its statement, the paper's formula and its code. The data (assets/lean-data.js) loads on demand.
(function () {
  'use strict';

  var L = null, CFG = null, APP = null;
  var built = false, loading = false, pending = null;
  var el = {};
  var st = { t: null, sel: -1, box: null, zoom: 1, usedBy: false, lay: null };
  var byShort = {}, byName = {}, byLast = {};
  var BOX_W = 300, GAP_X = 48, GAP_Y = 64, PAD = 28, PAD_TOP = 76, ZMIN = 0.2, ZMAX = 2;
  var STATUS_CHIP = { proved: 'Proved', cited: 'Proved using the cited results', external: 'Cited result', def: 'Definition' };
  var KW = words('theorem lemma def structure abbrev instance class inductive where by fun have show let in open namespace ' +
    'section end variable variables universe import noncomputable private protected if then else match with calc obtain ' +
    'refine exact intro intros rcases rintro simp simp_all rw rwa apply use constructor at only this omit include ' +
    'set_option example deriving extends mutual termination_by decreasing_by suffices from fun λ forall exists');
  var TAC = words('linarith nlinarith positivity norm_num ring ring_nf field_simp gcongr exact_mod_cast push_cast fun_prop ' +
    'continuity measurability aesop omega decide tauto trivial congr ext funext filter_upwards convert specialize ' +
    'split_ifs by_contra by_cases induction cases nth_rewrite conv unfold dsimp change exacts left right symm trans ' +
    'norm_cast bound refine_lift subst injection contradiction absurd exfalso assumption rfl sorry');
  var ID0 = 'A-Za-z_À-ɏͰ-Ͽἀ-῿℀-⅏';
  var TOK = new RegExp('/-[\\s\\S]*?-/|--[^\\n]*|"(?:\\\\.|[^"\\\\])*"|[' + ID0 + '][' + ID0 +
    '0-9\'!?⁰-ₜ.]*|\\d+(?:\\.\\d+)?|[\\s\\S]', 'g');
  var ID_START = new RegExp('^[' + ID0 + ']');

  function words(s) { var o = {}; s.split(/\s+/).forEach(function (w) { if (w) o[w] = 1; }); return o; }
  function esc(s) {
    return String(s == null ? '' : s).replace(/[&<>"]/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c];
    });
  }
  function store(key, val) {
    try {
      if (val === undefined) { var s = localStorage.getItem(key); return s ? JSON.parse(s) : null; }
      localStorage.setItem(key, JSON.stringify(val));
    } catch (e) { /* storage blocked: nothing is remembered */ }
    return null;
  }
  function storeIn(key, sub, val) { var o = store(key) || {}; o[sub] = val; store(key, o); }
  function q(sel, root) { return (root || el.root).querySelector(sel); }
  function qa(sel, root) { return Array.prototype.slice.call((root || el.root).querySelectorAll(sel)); }

  // ------------------------------------------------------------------------------------------------ loading

  function load(cb) {
    if (window.FLUP_LEAN) { L = window.FLUP_LEAN; cb(); return; }
    pending = cb;
    if (loading) return;
    loading = true;
    var s = document.createElement('script');
    s.src = CFG.leanData;
    s.onload = function () { L = window.FLUP_LEAN; if (pending) pending(); };
    s.onerror = function () {
      el.root.innerHTML = '<p class="wrap lean-loading">The Lean data could not be loaded. Reload the page to try again.</p>';
    };
    document.head.appendChild(s);
  }

  function prepare() {
    L.n.forEach(function (n, i) {
      byName[n] = i;
      byShort[L.d[i].s] = i;
      var last = n.split('.').pop();
      byLast[last] = Object.prototype.hasOwnProperty.call(byLast, last) ? -1 : i;
    });
  }

  function lookup(name) {
    if (!name) return -1;
    if (byShort[name] !== undefined) return byShort[name];
    if (byName[name] !== undefined) return byName[name];
    return -1;
  }

  // ------------------------------------------------------------------------------------------------ entry point

  function show(params) {
    CFG = window.FLUP_CFG;
    APP = window.FLUPApp;
    el.root = document.querySelector('#v-lean .lean-root');
    load(function () {
      if (!built) { prepare(); build(); built = true; }
      var t = params.t && L.trees[params.t] ? params.t : (st.t || CFG.defaults.g);
      var n = lookup(params.n);
      if (n >= 0 && L.d[n].b[t] === undefined) t = L.d[n].t[0];
      if (n < 0 && params.b && !boxOf(t, params.b)) {
        var t2 = treeWithBox(params.b);
        if (t2) t = t2;
      }
      setTree(t);
      if (n >= 0) select(n, true);
      else if (params.b) focusBox(params.b);
      else if (st.sel >= 0 && L.d[st.sel].b[t] !== undefined) select(st.sel, false);
      else writeHash();
    });
  }

  function boxOf(t, id) {
    var T = L.trees[t];
    for (var k = 0; k < T.boxes.length; k++) {
      if (T.boxes[k].id === id || T.boxes[k].module === id) return T.boxes[k];
    }
    return null;
  }

  function treeWithBox(id) {
    for (var k = 0; k < L.order.length; k++) if (boxOf(L.order[k], id)) return L.order[k];
    return null;
  }

  // ------------------------------------------------------------------------------------------------ skeleton

  function build() {
    var V = CFG.leanView;
    var pick = L.order.map(function (tid) {
      var T = L.trees[tid];
      return '<button type="button" role="radio" class="seg" data-tree="' + tid + '" data-set="' + tid + '" aria-checked="false" title="' +
        esc(T.sub) + '"><span class="dot"></span>' + T.label + '</button>';
    }).join('');
    var legend = ['proved', 'cited', 'external', 'def'].map(function (k) {
      return '<span class="lk-lg s-' + k + '"><span class="sd"></span>' + L.legend[k] + '</span>';
    }).join('') + '<span class="lk-lg"><span class="sh">shared</span>used by several of the results</span>' +
      '<span class="lk-lg"><span class="lk-d side lk-demo"><span class="nm">name</span></span>formalizes the paper\'s text of a step; this result\'s Lean proof does not use it</span>' +
      '<span class="lk-lg"><svg width="34" height="10" aria-hidden="true"><path class="use" d="M2,5 H28" /><path class="use-h" d="M26,1 L32,5 L26,9 z"/></svg>uses</span>' +
      '<span class="lk-lg"><svg width="34" height="10" aria-hidden="true"><path class="by" d="M2,5 H28" /><path class="by-h" d="M26,1 L32,5 L26,9 z"/></svg>used by</span>';
    el.root.innerHTML =
      '<div class="wrap lean-head">' +
        '<div class="segs lean-pick" role="radiogroup" aria-label="Result">' + pick + '</div>' +
        '<p class="lean-sum"></p>' +
        '<h2 class="lean-title"></h2>' +
        '<p class="lean-hint">' + V.hint + '</p>' +
        '<details class="lean-about"><summary>About this formalization</summary><div class="lean-about-body">' + V.about +
          '<p class="muted small">Lean ' + esc(V.toolchain) + ', Mathlib ' + esc(V.mathlib) + '. This page shows ' + L.n.length +
          ' declarations; ' + L.excluded + ' declarations that Lean generates automatically (constructors, recursors, equation ' +
          'lemmas) are left out.</p></div></details>' +
      '</div>' +
      '<div class="lean-main">' +
        '<div class="lk-col">' +
          '<div class="lk-frame">' +
            '<div class="lk-tools lk-tools-l"><button type="button" class="lk-btn" data-act="collapse">Collapse all</button>' +
              '<button type="button" class="lk-btn" data-act="expand">Expand all</button>' +
              '<label class="lk-btn lk-check"><input type="checkbox" class="lk-usedby"> Used by</label></div>' +
            '<div class="lk-tools lk-tools-r"><button type="button" class="lk-btn" data-act="out" aria-label="Zoom out">−</button>' +
              '<span class="lk-zoom" aria-live="polite">100%</span>' +
              '<button type="button" class="lk-btn" data-act="in" aria-label="Zoom in">+</button>' +
              '<button type="button" class="lk-btn" data-act="fit">Fit</button></div>' +
            '<div class="lk-viewport" tabindex="0" aria-label="Tree of the formalization"><div class="lk-sizer"><div class="lk-canvas">' +
              '<svg class="lk-edges" aria-hidden="true"></svg><div class="lk-boxes"></div><svg class="lk-arrows" aria-hidden="true"></svg>' +
            '</div></div></div>' +
          '</div>' +
          '<div class="lk-legend">' + legend + '</div>' +
        '</div>' +
        '<div class="lk-split" role="separator" aria-orientation="vertical" aria-label="Resize the panel" tabindex="0"></div>' +
        '<aside class="lk-panel" aria-live="polite" aria-label="Selected declaration"></aside>' +
      '</div>';
    el.pick = q('.lean-pick');
    el.sum = q('.lean-sum');
    el.title = q('.lean-title');
    el.main = q('.lean-main');
    el.frame = q('.lk-frame');
    el.vp = q('.lk-viewport');
    el.sizer = q('.lk-sizer');
    el.canvas = q('.lk-canvas');
    el.edges = q('.lk-edges');
    el.boxes = q('.lk-boxes');
    el.arrows = q('.lk-arrows');
    el.panel = q('.lk-panel');
    el.zoom = q('.lk-zoom');
    APP.renderMath(q('.lean-head'), true);
    APP.renderMath(q('.lk-legend'), true);
    var w = store('flup-lean-panel');
    if (w) el.main.style.setProperty('--lk-panel', w + 'px');
    wire();
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(function () { if (st.t) relayout(); });
  }

  // ------------------------------------------------------------------------------------------------ trees and boxes

  function isShared(d) {
    var k = 0;
    for (var j = 0; j < d.t.length; j++) if (L.main.indexOf(d.t[j]) >= 0) k++;
    return k > 1;
  }

  function nameHtml(s) { return esc(s).replace(/([._])/g, '$1<wbr>'); }

  function boxHtml(b, open, side) {
    var rows = b.decls.map(function (i) {
      var d = L.d[i];
      return '<button type="button" class="lk-d s-' + d.st + (side[i] ? ' side' : '') + '" data-i="' + i + '" title="' + esc(d.s) +
        (side[i] ? ' (not used by the Lean proof of this result)' : '') + '">' +
        '<span class="sd" aria-hidden="true"></span><span class="nm">' + nameHtml(d.s) + '</span>' +
        (isShared(d) ? '<span class="sh">shared</span>' : '') + '</button>';
    }).join('');
    var n = b.decls.length;
    return '<section class="lk-box k-' + b.kind + (open ? ' open' : '') + '" data-box="' + b.id + '">' +
      '<header class="lk-bh"><button type="button" class="lk-fold" aria-expanded="' + (open ? 'true' : 'false') +
        '" aria-label="Show or hide the declarations"' + (n ? '' : ' disabled') + '><svg viewBox="0 0 16 16" aria-hidden="true"><path d="M6 3.5l4.5 4.5L6 12.5"/></svg></button>' +
        '<span class="chip">' + esc(b.chip) + '</span><span class="lk-n">' + n + ' declaration' + (n === 1 ? '' : 's') + '</span>' +
        '<span class="lk-hits" aria-hidden="true"></span></header>' +
      '<button type="button" class="lk-bl" data-boxsel="' + b.id + '">' + b.label + '</button>' +
      (b.sub ? '<p class="lk-bs">' + b.sub + '</p>' : '') +
      (n ? '<div class="lk-list">' + rows + '</div>' : '<p class="lk-empty">No declaration of its own: this step is carried out inside the declarations of the neighbouring steps.</p>') +
      '</section>';
  }

  function summaryHtml(T) {
    var c = T.counts, parts = ['<span><b>' + T.total + '</b> declarations</span>'];
    if (c.proved) parts.push('<span class="s-proved"><span class="sd"></span><b>' + c.proved + '</b> proved</span>');
    if (c.cited) parts.push('<span class="s-cited"><span class="sd"></span><b>' + c.cited + '</b> proved using the cited results</span>');
    if (c.external) parts.push('<span class="s-external"><span class="sd"></span><b>' + c.external + '</b> cited</span>');
    if (c.def) parts.push('<span class="s-def"><span class="sd"></span><b>' + c.def + '</b> definitions</span>');
    parts.push(T.ownAxioms.length ? '<span class="warn">axioms: ' + esc(T.ownAxioms.join(', ')) + '</span>' : '<span>no axioms of its own</span>');
    if (T.side && T.side.length) parts.push('<span class="lk-sidenote">' + T.side.length + ' formalize the paper\'s text of a step without being used by this proof</span>');
    return parts.join('<span class="sep"> · </span>');
  }

  function setTree(tid, keepSel) {
    if (st.t === tid && el.boxes.childNodes.length) return;
    st.t = tid;
    var T = L.trees[tid];
    qa('.seg', el.pick).forEach(function (b) {
      var on = b.getAttribute('data-tree') === tid;
      b.setAttribute('aria-checked', on ? 'true' : 'false');
      b.tabIndex = on ? 0 : -1;
    });
    el.root.setAttribute('data-set', tid);
    el.sum.innerHTML = summaryHtml(T);
    el.title.innerHTML = (L.main.indexOf(tid) >= 0 ? 'The formalization of ' : '') + T.label +
      (T.sub ? ' <span class="lean-sub">' + esc(T.sub) + '</span>' : '');
    APP.renderMath(el.title, true);
    var folds = (store('flup-lean-folds') || {})[tid] || {};
    st.side = {};
    (T.side || []).forEach(function (i) { st.side[i] = 1; });
    el.boxes.innerHTML = T.boxes.map(function (b) {
      var open = Object.prototype.hasOwnProperty.call(folds, b.id) ? folds[b.id] : b.id === 'root';
      return boxHtml(b, open && b.decls.length > 0, st.side);
    }).join('');
    APP.renderMath(el.boxes, true);
    if (boxRO) { boxRO.disconnect(); qa('.lk-box', el.boxes).forEach(function (b) { boxRO.observe(b); }); }
    if (!keepSel) { st.sel = -1; st.box = null; }
    layout();
    var z = (store('flup-lean-zoom') || {})[tid];
    if (z) setZoom(z); else fitWidth();
    el.vp.scrollTop = 0;
    el.vp.scrollLeft = 0;
    if (!keepSel) { drawArrows(); panelForTree(); }
  }

  function boxNode(id) { return el.boxes.querySelector('.lk-box[data-box="' + id + '"]'); }

  function layout() {
    var T = L.trees[st.t];
    var cols = T.boxes.map(function (b) { return b.col; });
    var c0 = Math.min.apply(null, cols), c1 = Math.max.apply(null, cols);
    var rows = {}, pos = {};
    T.boxes.forEach(function (b) {
      var node = boxNode(b.id);
      node.style.width = BOX_W + 'px';
      (rows[b.row] = rows[b.row] || []).push([b, node, node.offsetHeight]);
    });
    var W = PAD * 2 + (c1 - c0 + 1) * BOX_W + (c1 - c0) * GAP_X, y = PAD_TOP;
    Object.keys(rows).map(Number).sort(function (a, b) { return a - b; }).forEach(function (r) {
      var hmax = 0;
      rows[r].forEach(function (e) {
        var x = PAD + (e[0].col - c0) * (BOX_W + GAP_X);
        e[1].style.left = x + 'px';
        e[1].style.top = y + 'px';
        pos[e[0].id] = { x: x, y: y, w: BOX_W, h: e[2], node: e[1] };
        hmax = Math.max(hmax, e[2]);
      });
      y += hmax + GAP_Y;
    });
    var H = y - GAP_Y + PAD;
    st.lay = { pos: pos, W: W, H: H };
    el.canvas.style.width = W + 'px';
    el.canvas.style.height = H + 'px';
    [el.edges, el.arrows].forEach(function (s) {
      s.setAttribute('width', W);
      s.setAttribute('height', H);
      s.setAttribute('viewBox', '0 0 ' + W + ' ' + H);
    });
    drawEdges();
    applyZoom();
  }

  function relayout() { layout(); drawArrows(); }
  // the boxes and arrows follow the content: lay out again whenever a box changes size (fonts, formulas, folding)
  var boxRO = 'ResizeObserver' in window ? new ResizeObserver(function () { queueRelayout(); }) : null, relayoutQueued = false;
  function queueRelayout() {
    if (relayoutQueued) return;
    relayoutQueued = true;
    requestAnimationFrame(function () {
      relayoutQueued = false;
      if (st.t && el.boxes && el.boxes.childNodes.length && el.root.offsetParent !== null) { layout(); drawArrows(); }
    });
  }

  function drawEdges() {
    var T = L.trees[st.t], P = st.lay.pos, out = [];
    T.boxes.forEach(function (b) {
      b.parents.forEach(function (pid) {
        var p = P[pid], c = P[b.id];
        if (!p || !c) return;
        var x1 = p.x + p.w / 2, y1 = p.y + p.h, x2 = c.x + c.w / 2, y2 = c.y;
        if (y2 < y1) { y1 = p.y; y2 = c.y + c.h; }
        var my = (y1 + y2) / 2;
        out.push('<path data-a="' + pid + '" data-b="' + b.id + '" d="M' + x1 + ',' + y1 + ' C' + x1 + ',' + my + ' ' + x2 + ',' + my +
          ' ' + x2 + ',' + y2 + '"/>');
      });
    });
    el.edges.innerHTML = out.join('');
  }

  // anchor of a declaration in the canvas: its row, or the header of its box when the box is folded
  function anchor(i) {
    var bid = L.d[i].b[st.t];
    if (bid === undefined) return null;
    var p = st.lay.pos[bid];
    if (!p) return null;
    if (p.node.classList.contains('open')) {
      var row = p.node.querySelector('.lk-d[data-i="' + i + '"]');
      if (row) return { x: p.x, w: p.w, y: p.y + row.offsetTop + row.offsetHeight / 2, box: bid };
    }
    return { x: p.x, w: p.w, y: p.y + 16, box: bid, folded: true };
  }

  function curve(a, b, cls) {
    var x1, x2, c1, c2, dy = Math.abs(b.y - a.y);
    if (Math.abs(a.x - b.x) < 2) {
      var bend = Math.min(150, 18 + dy * 0.22);
      x1 = a.x; x2 = b.x - 2; c1 = x1 - bend; c2 = x2 - bend;
    } else if (b.x > a.x) {
      x1 = a.x + a.w; x2 = b.x - 2;
      var k = Math.max(30, (x2 - x1) / 2); c1 = x1 + k; c2 = x2 - k;
    } else {
      x1 = a.x; x2 = b.x + b.w + 2;
      var k2 = Math.max(30, (x1 - x2) / 2); c1 = x1 - k2; c2 = x2 + k2;
    }
    return '<path class="' + cls + '" d="M' + x1 + ',' + a.y + ' C' + c1 + ',' + a.y + ' ' + c2 + ',' + b.y + ' ' + x2 + ',' + b.y +
      '" marker-end="url(#lk-ah-' + cls + ')"/>';
  }

  var DEFS = '<defs><marker id="lk-ah-use" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">' +
    '<path d="M0,0 L10,5 L0,10 z" class="use-h"/></marker><marker id="lk-ah-by" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" ' +
    'markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="by-h"/></marker></defs>';

  function drawArrows() {
    var out = [DEFS];
    qa('.lk-edges path.on', el.canvas).forEach(function (p) { p.classList.remove('on'); });
    if (st.sel >= 0 && st.lay) {
      var a = anchor(st.sel), d = L.d[st.sel];
      if (a) {
        var seen = {};
        d.u.forEach(function (j) {
          var b = anchor(j);
          if (!b) return;
          var key = b.folded ? 'f' + b.box : 'r' + j;
          if (seen[key]) return;
          seen[key] = 1;
          out.push(curve(a, b, 'use'));
        });
        if (st.usedBy) {
          var seen2 = {};
          d.ub.forEach(function (j) {
            var b = anchor(j);
            if (!b) return;
            var key = b.folded ? 'f' + b.box : 'r' + j;
            if (seen2[key]) return;
            seen2[key] = 1;
            out.push(curve(b, a, 'by'));
          });
        }
      }
    }
    if (st.box) {
      qa('.lk-edges path', el.canvas).forEach(function (p) {
        if (p.getAttribute('data-a') === st.box || p.getAttribute('data-b') === st.box) p.classList.add('on');
      });
    }
    el.arrows.innerHTML = out.join('');
  }

  // ------------------------------------------------------------------------------------------------ zoom and pan

  function applyZoom() {
    if (!st.lay) return;
    el.canvas.style.transform = 'scale(' + st.zoom + ')';
    el.sizer.style.width = Math.ceil(st.lay.W * st.zoom) + 'px';
    el.sizer.style.height = Math.ceil(st.lay.H * st.zoom) + 'px';
    el.zoom.textContent = Math.round(st.zoom * 100) + '%';
  }

  function setZoom(z, remember) {
    st.zoom = Math.max(ZMIN, Math.min(ZMAX, z));
    applyZoom();
    if (remember) storeIn('flup-lean-zoom', st.t, st.zoom);
  }

  function zoomAt(z, cx, cy) {
    var s1 = el.sizer.getBoundingClientRect(), u = (cx - s1.left) / st.zoom, v = (cy - s1.top) / st.zoom;
    setZoom(z, true);
    var s2 = el.sizer.getBoundingClientRect();
    el.vp.scrollLeft += s2.left + u * st.zoom - cx;
    el.vp.scrollTop += s2.top + v * st.zoom - cy;
  }

  function zoomCenter(f) {
    var r = el.vp.getBoundingClientRect();
    zoomAt(st.zoom * f, r.left + r.width / 2, r.top + r.height / 2);
  }

  function fitWidth() {
    var w = el.vp.clientWidth - 8;
    setZoom(Math.min(1, w / st.lay.W), false);
  }

  function fit() {
    var w = el.vp.clientWidth - 8, h = el.vp.clientHeight - 8;
    setZoom(Math.min(1, w / st.lay.W, h / st.lay.H), true);
    el.vp.scrollTop = 0;
    el.vp.scrollLeft = 0;
  }

  function scrollToCanvas(x, y, w, h) {
    var z = st.zoom, vw = el.vp.clientWidth, vh = el.vp.clientHeight;
    var left = el.sizer.offsetLeft + x * z, top = el.sizer.offsetTop + y * z;
    var tx = left - Math.max(16, (vw - w * z) / 2), ty = top - Math.max(16, (vh - h * z) / 2);
    if (h * z > vh) ty = top - 24;
    el.vp.scrollTo({ left: Math.max(0, tx), top: Math.max(0, ty), behavior: 'smooth' });
  }

  // ------------------------------------------------------------------------------------------------ selection

  function setOpen(bid, open) {
    var node = boxNode(bid);
    if (!node || !node.querySelector('.lk-list')) return false;
    if (node.classList.contains('open') === open) return false;
    node.classList.toggle('open', open);
    node.querySelector('.lk-fold').setAttribute('aria-expanded', open ? 'true' : 'false');
    var o = store('flup-lean-folds') || {};
    (o[st.t] = o[st.t] || {})[bid] = open;
    store('flup-lean-folds', o);
    return true;
  }

  function mark() {
    qa('.is-sel,.is-use,.is-by', el.boxes).forEach(function (n) { n.classList.remove('is-sel', 'is-use', 'is-by'); });
    qa('.lk-box', el.boxes).forEach(function (b) { b.classList.remove('box-sel', 'has-hit'); q('.lk-hits', b).textContent = ''; });
    if (st.box) { var bn = boxNode(st.box); if (bn) bn.classList.add('box-sel'); }
    if (st.sel < 0) return;
    var d = L.d[st.sel], hits = {};
    function one(j, cls) {
      var row = el.boxes.querySelector('.lk-d[data-i="' + j + '"]');
      if (!row) return;
      row.classList.add(cls);
      if (cls !== 'is-sel') {
        var box = row.closest('.lk-box');
        if (!box.classList.contains('open')) {
          var id = box.getAttribute('data-box');
          hits[id] = (hits[id] || 0) + 1;
        }
      }
    }
    one(st.sel, 'is-sel');
    d.u.forEach(function (j) { one(j, 'is-use'); });
    if (st.usedBy) d.ub.forEach(function (j) { one(j, 'is-by'); });
    Object.keys(hits).forEach(function (id) {
      var b = boxNode(id);
      b.classList.add('has-hit');
      q('.lk-hits', b).textContent = hits[id] + ' linked';
    });
  }

  function select(i, scroll) {
    var d = L.d[i];
    if (d.b[st.t] === undefined) setTree(d.t[0], true);
    st.sel = i;
    st.box = null;
    var bid = d.b[st.t];
    if (setOpen(bid, true)) layout();
    mark();
    drawArrows();
    renderPanel(i);
    if (scroll) {
      var a = anchor(i);
      if (a) scrollToCanvas(a.x, a.y - 40, a.w, 80);
    }
    writeHash();
  }

  function selectBox(bid, scroll) {
    st.sel = -1;
    st.box = bid;
    mark();
    drawArrows();
    panelForBox(bid);
    if (scroll) {
      var p = st.lay.pos[bid];
      if (p) scrollToCanvas(p.x, p.y, p.w, Math.min(p.h, 400));
    }
    writeHash();
  }

  function focusBox(id) {
    var b = boxOf(st.t, id);
    if (!b) return;
    if (setOpen(b.id, true)) relayout();
    selectBox(b.id, true);
    var node = boxNode(b.id);
    node.classList.remove('flash');
    void node.offsetWidth;
    node.classList.add('flash');
  }

  function writeHash() {
    if (!APP || APP.currentView() !== 'lean') return;
    var h = '#/lean/' + st.t + (st.sel >= 0 ? '?n=' + encodeURIComponent(L.d[st.sel].s) : (st.box ? '?b=' + st.box : ''));
    if (location.hash !== h) history.replaceState(null, '', h);
  }

  // ------------------------------------------------------------------------------------------------ panel

  function stepLink(module, text) {
    return '<a class="lp-go" href="' + APP.stepHref(st.t, module) + '">' + text + '</a>';
  }

  function refHtml(j) {
    var d = L.d[j], here = d.b[st.t] !== undefined;
    return '<button type="button" class="lk-ref s-' + d.st + '" data-i="' + j + '"><span class="sd"></span>' + nameHtml(d.s) + '</button>' +
      (here ? '' : '<span class="lp-other">(other result)</span>');
  }

  function relHtml(label, list, cls) {
    if (!list.length) return '<div class="lp-rel ' + cls + '"><span class="lp-k">' + label + '</span><span class="muted">no other declaration</span></div>';
    var first = list.slice(0, 24).map(refHtml).join(''), rest = list.slice(24).map(refHtml).join('');
    return '<div class="lp-rel ' + cls + '"><span class="lp-k">' + label + '</span>' + first +
      (rest ? '<details class="lp-more"><summary>' + (list.length - 24) + ' more</summary>' + rest + '</details>' : '') + '</div>';
  }

  function treeButtons(ts) {
    return ts.map(function (t) {
      return '<button type="button" class="lk-tree" data-tree="' + t + '" data-set="' + t + '"><span class="dot"></span>' + L.trees[t].label + '</button>';
    }).join('');
  }

  function renderPanel(i) {
    var d = L.d[i], bid = d.b[st.t], box = boxOf(st.t, bid);
    var mains = d.t.filter(function (t) { return L.main.indexOf(t) >= 0; });
    var dot = d.s.lastIndexOf('.'), ns = dot > 0 ? d.s.slice(0, dot + 1) : '';
    var isDef = d.st === 'def' || (d.k === 'structure' && d.st !== 'external');
    var h = '<p class="lp-chips"><span class="chip chip-kind">' + esc(d.k) + '</span><span class="chip chip-st s-' + d.st + '"><span class="sd"></span>' +
      STATUS_CHIP[d.st] + '</span>' + (mains.length > 1 ? '<span class="chip chip-sh">Shared by ' + mains.length + ' results</span>' : '') + '</p>' +
      '<h3 class="lp-name">' + (ns ? '<span class="lp-ns">' + nameHtml(ns) + '</span>' : '') + nameHtml(d.s.slice(ns.length)) + '</h3>' +
      (st.side && st.side[i] ? '<p class="lp-note">The Lean proof of ' + L.trees[st.t].label + ' does not use this declaration: it ' +
        'formalizes the paper\'s text of this step.</p>' : '') +
      (box ? '<p class="lp-box"><button type="button" class="chip" data-boxsel="' + box.id + '">' + esc(box.chip) + '</button> <span>' + box.label + '</span></p>' : '') +
      '<p class="lp-file">' + esc(d.f) + (d.l ? ', lines ' + d.l + '–' + d.e : '') + '</p>' +
      relHtml('Uses', d.u, 'lp-uses') + relHtml('Used by', d.ub, 'lp-by') +
      '<div class="lp-rel"><span class="lp-k">Axioms</span><span>' + esc(L.axsets[d.a].join(', ') || 'none') + '</span></div>' +
      (d.r.length ? '<div class="lp-rel"><span class="lp-k">Rests on</span>' + d.r.map(function (r) {
        var j = lookup(r);
        return j >= 0 ? refHtml(j) : '<code>' + esc(r) + '</code>';
      }).join('') + '<span class="lp-other">cited results, taken as hypotheses</span></div>' : '') +
      (mains.length > 1 ? '<div class="lp-rel"><span class="lp-k">Results</span>' + treeButtons(mains) + '</div>' : '') +
      (d.stmt || d.doc ? '<div class="lp-card"><p class="lp-k">' + (isDef ? 'Definition' : 'Statement') + '</p>' +
        (d.stmt || '<p>' + esc(d.doc) + '</p>') + '</div>' : '') +
      (d.pp ? '<div class="lp-card lp-paper"><p class="lp-k">Paper ' + esc(d.pl) + '</p>' + d.pp +
        (d.pm ? '<p><a class="lp-go" href="#/r/' + d.pm + '">Its page: plain words, idea and proof →</a></p>' : '') + '</div>' : '') +
      (d.m.length ? '<p class="lp-items">In the paper: ' + d.m.map(function (x) { return '<a class="lp-go" href="#/r/' + x[1] + '">' + esc(x[0]) + '</a>'; }).join(', ') + '</p>' : '') +
      '<div class="lp-card lp-code"><pre><code>' + highlight(d.c, d.ns) + '</code></pre></div>';
    el.panel.innerHTML = h;
    APP.renderMath(el.panel, true);
    el.panel.scrollTop = 0;
  }

  function panelForBox(bid) {
    var T = L.trees[st.t], b = boxOf(st.t, bid);
    if (!b) return;
    var counts = { proved: 0, cited: 0, external: 0, def: 0 };
    b.decls.forEach(function (i) { counts[L.d[i].st]++; });
    var above = b.parents.map(function (p) { return boxOf(st.t, p); }).filter(Boolean);
    var below = T.boxes.filter(function (x) { return x.parents.indexOf(b.id) >= 0; });
    function boxLinks(list) {
      return list.map(function (x) { return '<button type="button" class="lk-boxref" data-boxsel="' + x.id + '"><span class="chip">' + esc(x.chip) + '</span> ' + x.label + '</button>'; }).join('');
    }
    var h = '<p class="lp-chips"><span class="chip">' + esc(b.chip) + '</span></p><h3 class="lp-title">' + b.label + '</h3>' +
      (b.sub ? '<p class="lp-file">' + b.sub + '</p>' : '') +
      '<p class="lean-sum">' + summaryHtml({ total: b.decls.length, counts: counts, ownAxioms: [] }).replace(/<span class="sep"> · <\/span>no axioms of its own$/, '') + '</p>' +
      (b.module ? '<p>' + stepLink(b.module, 'Read this step in the text →') + '</p>' : '') +
      (above.length ? '<div class="lp-rel"><span class="lp-k">Used in</span>' + boxLinks(above) + '</div>' : '') +
      (below.length ? '<div class="lp-rel"><span class="lp-k">Rests on</span>' + boxLinks(below) + '</div>' : '') +
      (b.decls.length ? '<div class="lp-rel lp-list"><span class="lp-k">Declarations</span>' + b.decls.map(refHtml).join('') + '</div>' :
        '<p class="muted">This step has no declaration of its own: in Lean it is carried out inside the declarations of the neighbouring steps.</p>');
    el.panel.innerHTML = h;
    APP.renderMath(el.panel, true);
    el.panel.scrollTop = 0;
  }

  function panelForTree() {
    var T = L.trees[st.t];
    var h = '<p class="lp-chips"><span class="chip">' + (L.main.indexOf(st.t) >= 0 ? 'Result' : 'Collection') + '</span></p>' +
      '<h3 class="lp-title">' + T.label + '</h3>' + (T.sub ? '<p class="lp-file">' + esc(T.sub) + '</p>' : '') +
      '<p class="lean-sum">' + summaryHtml(T) + '</p>' +
      (T.root != null ? '<p>Start from the theorem: <span class="lp-start">' + refHtml(T.root) + '</span></p>' : '') +
      '<p class="muted">Click a declaration to see its statement, the paper\'s formula and its Lean code, with arrows to what it uses. ' +
      'Click the title of a box to see the step.</p>';
    el.panel.innerHTML = h;
    APP.renderMath(el.panel, true);
  }

  // ------------------------------------------------------------------------------------------------ code

  function resolve(tok, ns) {
    for (var k = 0; k < ns.length; k++) {
      var j = byName[ns[k] + '.' + tok];
      if (j !== undefined) return j;
    }
    if (byName['FLUP.' + tok] !== undefined) return byName['FLUP.' + tok];
    if (byName[tok] !== undefined) return byName[tok];
    if (tok.indexOf('.') < 0 && tok.length >= 5 && byLast[tok] !== undefined && byLast[tok] >= 0) return byLast[tok];
    return -1;
  }

  function highlight(code, ns) {
    var out = [], m;
    TOK.lastIndex = 0;
    while ((m = TOK.exec(code))) {
      var t = m[0], c0 = t.charAt(0);
      if (c0 === '/' && t.charAt(1) === '-') out.push('<span class="lk-c' + (t.charAt(2) === '-' ? ' lk-doc' : '') + '">' + esc(t) + '</span>');
      else if (c0 === '-' && t.charAt(1) === '-') out.push('<span class="lk-c">' + esc(t) + '</span>');
      else if (c0 === '"') out.push('<span class="lk-s">' + esc(t) + '</span>');
      else if (/\d/.test(c0)) out.push('<span class="lk-num">' + esc(t) + '</span>');
      else if (ID_START.test(c0)) {
        var base = t.replace(/\.+$/, ''), tail = t.slice(base.length);
        if (KW[base]) out.push('<span class="lk-k">' + esc(base) + '</span>' + esc(tail));
        else if (TAC[base]) out.push('<span class="lk-t">' + esc(base) + '</span>' + esc(tail));
        else {
          var j = resolve(base, ns);
          out.push(j >= 0 ? '<a class="lk-ref" data-i="' + j + '" href="#/lean/' + st.t + '?n=' + encodeURIComponent(L.d[j].s) + '">' +
            esc(base) + '</a>' + esc(tail) : esc(t));
        }
      } else out.push(esc(t));
    }
    return out.join('');
  }

  // ------------------------------------------------------------------------------------------------ events

  function wire() {
    el.root.addEventListener('click', function (e) {
      var t = e.target.closest('[data-i],[data-boxsel],[data-tree],[data-act],.lk-fold');
      if (!t || !el.root.contains(t)) return;
      if (t.classList.contains('lk-fold')) {
        var bid = t.closest('.lk-box').getAttribute('data-box');
        setOpen(bid, !t.closest('.lk-box').classList.contains('open'));
        relayout();
        mark();
        return;
      }
      if (t.hasAttribute('data-i')) {
        e.preventDefault();
        select(Number(t.getAttribute('data-i')), !t.classList.contains('lk-d'));
        return;
      }
      if (t.hasAttribute('data-boxsel')) { selectBox(t.getAttribute('data-boxsel'), !el.canvas.contains(t)); return; }
      if (t.hasAttribute('data-tree')) {
        var keep = st.sel;
        setTree(t.getAttribute('data-tree'));
        if (keep >= 0 && L.d[keep].b[st.t] !== undefined) select(keep, true); else writeHash();
        return;
      }
      var act = t.getAttribute('data-act');
      if (act === 'in') zoomCenter(1.25);
      else if (act === 'out') zoomCenter(1 / 1.25);
      else if (act === 'fit') fit();
      else if (act === 'collapse' || act === 'expand') {
        L.trees[st.t].boxes.forEach(function (b) { setOpen(b.id, act === 'expand'); });
        if (st.sel >= 0 && act === 'collapse') { /* the selection stays; its arrows point at the folded boxes */ }
        relayout();
        mark();
      }
    });
    q('.lk-usedby').addEventListener('change', function (e) { st.usedBy = e.target.checked; mark(); drawArrows(); });
    // keyboard on the picker
    el.pick.addEventListener('keydown', function (e) {
      if (['ArrowRight', 'ArrowDown', 'ArrowLeft', 'ArrowUp'].indexOf(e.key) < 0) return;
      var bs = qa('.seg', el.pick), k = bs.indexOf(document.activeElement);
      if (k < 0) return;
      e.preventDefault();
      var n = bs[(k + (e.key === 'ArrowRight' || e.key === 'ArrowDown' ? 1 : bs.length - 1)) % bs.length];
      n.focus();
      n.click();
    });
    // Ctrl + wheel and trackpad pinch
    el.vp.addEventListener('wheel', function (e) {
      if (!e.ctrlKey && !e.metaKey) return;
      e.preventDefault();
      zoomAt(st.zoom * Math.exp(-e.deltaY * 0.0022), e.clientX, e.clientY);
    }, { passive: false });
    // drag the background (mouse) and pinch (touch)
    var drag = null, touches = {}, pinch = null;
    el.vp.addEventListener('pointerdown', function (e) {
      if (e.pointerType === 'touch') {
        touches[e.pointerId] = { x: e.clientX, y: e.clientY };
        var ids = Object.keys(touches);
        if (ids.length === 2) {
          var a = touches[ids[0]], b = touches[ids[1]];
          pinch = { d: Math.hypot(a.x - b.x, a.y - b.y), z: st.zoom };
        }
        return;
      }
      if (e.button !== 0 || e.target.closest('.lk-box,.lk-tools')) return;
      drag = { x: e.clientX, y: e.clientY, l: el.vp.scrollLeft, t: el.vp.scrollTop };
      el.vp.setPointerCapture(e.pointerId);
      el.vp.classList.add('dragging');
    });
    el.vp.addEventListener('pointermove', function (e) {
      if (e.pointerType === 'touch') {
        if (!touches[e.pointerId]) return;
        touches[e.pointerId] = { x: e.clientX, y: e.clientY };
        var ids = Object.keys(touches);
        if (pinch && ids.length === 2) {
          var a = touches[ids[0]], b = touches[ids[1]];
          zoomAt(pinch.z * Math.hypot(a.x - b.x, a.y - b.y) / pinch.d, (a.x + b.x) / 2, (a.y + b.y) / 2);
        }
        return;
      }
      if (!drag) return;
      el.vp.scrollLeft = drag.l - (e.clientX - drag.x);
      el.vp.scrollTop = drag.t - (e.clientY - drag.y);
    });
    function end(e) {
      if (e.pointerType === 'touch') { delete touches[e.pointerId]; if (Object.keys(touches).length < 2) pinch = null; return; }
      if (drag) { drag = null; el.vp.classList.remove('dragging'); }
    }
    el.vp.addEventListener('pointerup', end);
    el.vp.addEventListener('pointercancel', end);
    // keyboard zoom inside the canvas
    el.vp.addEventListener('keydown', function (e) {
      if (e.key === '+' || e.key === '=') { zoomCenter(1.25); e.preventDefault(); }
      else if (e.key === '-') { zoomCenter(1 / 1.25); e.preventDefault(); }
      else if (e.key === '0') { fit(); e.preventDefault(); }
    });
    // splitter
    var split = q('.lk-split'), sdrag = null;
    function setPanel(w) {
      var max = Math.max(360, el.main.clientWidth * 0.62);
      w = Math.max(300, Math.min(max, w));
      el.main.style.setProperty('--lk-panel', Math.round(w) + 'px');
      store('flup-lean-panel', Math.round(w));
    }
    split.addEventListener('pointerdown', function (e) { sdrag = true; split.setPointerCapture(e.pointerId); split.classList.add('on'); });
    split.addEventListener('pointermove', function (e) {
      if (!sdrag) return;
      setPanel(el.main.getBoundingClientRect().right - e.clientX);
    });
    split.addEventListener('pointerup', function () { sdrag = false; split.classList.remove('on'); });
    split.addEventListener('keydown', function (e) {
      var w = el.panel.getBoundingClientRect().width;
      if (e.key === 'ArrowLeft') { setPanel(w + 24); e.preventDefault(); }
      if (e.key === 'ArrowRight') { setPanel(w - 24); e.preventDefault(); }
    });
  }

  window.FLUPLean = { show: show };
})();
