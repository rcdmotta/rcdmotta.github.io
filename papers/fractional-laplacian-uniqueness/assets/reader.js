// Reading companion: the opening (question, figure, results), a guided reading in chapters, one page per result
// (plain words, statement, main idea, proof), explanations that open next to the passage, a finder, the Ideas Map
// and the Lean Map (with a way back to the passage), and the seminar. The texts come from assets/reader-data.js.
// Addresses: #/  #/read/CHAPTER  #/r/RESULT[/statement|/idea|/proof|/step/MODULE]  #/find?q=  #/ideas/TREE[/NODE]
//            #/lean/TREE[?n=DECLARATION|?b=BOX]  #/talk[/SLIDE]
(function () {
  'use strict';

  var CFG = JSON.parse(document.getElementById('site-config').textContent);
  var MACROS = {};
  try { MACROS = JSON.parse(document.getElementById('katex-macros').textContent); } catch (e) { MACROS = {}; }
  window.FLUP_CFG = CFG;
  var D = null, waiting = [], loading = false;
  var S = { view: null, back: null, pendingAnchor: null, tree: null, node: null, td: 'ideas' };
  var FAMILY = { uniqueness: 'Uniqueness', 'non-uniqueness': 'Non-uniqueness', application: 'Application',
    preliminary: 'Preliminaries', term: 'Term' };

  function $(sel, root) { return (root || document).querySelector(sel); }
  function $$(sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); }
  function esc(s) {
    return String(s == null ? '' : s).replace(/[&<>"]/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c];
    });
  }
  function strip(h) { var d = document.createElement('div'); d.innerHTML = h; return d.textContent; }
  // the short name of a main result (UP, NUP, ...), shown after its number
  function tagHtml(r) { return r && r.tag ? ' <span class="rtag fam-' + esc(r.family) + '">' + esc(r.tag) + '</span>' : ''; }
  try { S.back = JSON.parse(sessionStorage.getItem('flup-back') || 'null'); } catch (e) { S.back = null; }

  // ------------------------------------------------------------------------------------------------ math

  function renderMath(el, force) {
    if (!el || !window.renderMathInElement) return;
    if (el.__math && !force) return;
    el.__math = true;
    try {
      window.renderMathInElement(el, {
        delimiters: [{ left: '\\[', right: '\\]', display: true }, { left: '\\(', right: '\\)', display: false }],
        macros: Object.assign({}, MACROS), throwOnError: false, strict: 'ignore',
        ignoredTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code', 'option', 'svg']
      });
    } catch (e) { /* a formula that KaTeX cannot parse stays as source */ }
    requestAnimationFrame(function () { fitMath(el); });
  }

  // Formulas keep the paper's layout. An inline formula stays on one line (it may break only if it is wider than
  // its column); a display that does not fit its column is scaled down, at most to 55%, and beyond that scrolls,
  // with its equation number after it instead of over it.
  function fitMath(root) {
    if (!root || root.offsetParent === null) return;
    $$('.katex-display', root).forEach(function (k) {
      if (k.offsetParent === null) return;
      var kx = k.querySelector('.katex'), html = k.querySelector('.katex-html');
      if (!kx || !html) return;
      kx.style.fontSize = '';
      k.classList.remove('fit-scroll');
      var avail = k.clientWidth;
      if (!avail) return;
      var base = 0, tag = html.querySelector('.tag');
      $$('.base', html).forEach(function (b) { base = Math.max(base, b.getBoundingClientRect().width); });
      var need = base + 2 * (tag ? tag.getBoundingClientRect().width : 0) + 6;
      if (need <= avail) return;
      var scale = Math.max(0.55, avail / need);
      kx.style.fontSize = (1.21 * scale).toFixed(3) + 'em';
      if (avail / need < 0.55) k.classList.add('fit-scroll');
    });
    $$('.katex', root).forEach(function (k) {
      if (k.closest('.katex-display')) return;
      k.classList.remove('wrap-ok');
      var host = k.parentNode.closest('p, li, div, td, aside, section');
      if (host && k.getBoundingClientRect().width > host.clientWidth) k.classList.add('wrap-ok');
    });
  }
  var fitTimer = null;
  window.addEventListener('resize', function () {
    clearTimeout(fitTimer);
    fitTimer = setTimeout(function () { fitMath($('#main > .view:not([hidden])')); }, 150);
  });
  // a passage opened later (a <details>) is fitted when it opens
  document.addEventListener('toggle', function (e) {
    if (e.target.open) { renderMath(e.target); fitMath(e.target); }
  }, true);

  // ------------------------------------------------------------------------------------------------ data

  function withData(cb) {
    if (window.FLUP_READER) { D = window.FLUP_READER; cb(); return; }
    waiting.push(cb);
    if (loading) return;
    loading = true;
    var s = document.createElement('script');
    s.src = CFG.readerData;
    s.onload = function () {
      D = window.FLUP_READER;
      var w = waiting;
      waiting = [];
      w.forEach(function (f) { f(); });
    };
    s.onerror = function () {
      var v = $('#v-read');
      v.innerHTML = '<p class="muted">The texts could not be loaded. Reload the page to try again.</p>';
      showView('read');
    };
    document.head.appendChild(s);
  }

  // ------------------------------------------------------------------------------------------------ routing

  function parse(hash) {
    var raw = (hash || '').replace(/^#\/?/, ''), k = raw.indexOf('?');
    var path = k < 0 ? raw : raw.slice(0, k), query = k < 0 ? '' : raw.slice(k + 1), params = {};
    query.split('&').forEach(function (kv) {
      if (!kv) return;
      var i = kv.indexOf('=');
      try { params[decodeURIComponent(i < 0 ? kv : kv.slice(0, i))] = decodeURIComponent(i < 0 ? '' : kv.slice(i + 1)); } catch (e) { /* ignore */ }
    });
    var parts = path.split('/').filter(function (x) { return x !== ''; }).map(function (x) {
      try { return decodeURIComponent(x); } catch (e) { return x; }
    });
    return { parts: parts, params: params };
  }

  // addresses of the first version of the site
  function legacy(h) {
    var raw = h.replace(/^#/, ''), p = parse('#/' + raw.replace(/^lean\?/, 'lean/?'));
    if (raw === 'motivation') return '#/read/' + CFG.firstChapter;
    if (raw === 'presentation' || /^slide-\d+$/.test(raw)) return '#/talk';
    if (raw.indexOf('lean') === 0) return '#/lean/' + (p.params.t || CFG.defaults.g) + (p.params.n ? '?n=' + encodeURIComponent(p.params.n) : '');
    if (raw.indexOf('interactive/tree') === 0) return '#/ideas/' + (parse('#/' + raw).params.t || CFG.defaults.g);
    if (raw.indexOf('interactive') === 0 || raw === 'preprint') return '#/';
    return null;
  }

  function route() {
    var h = location.hash;
    if (h && h !== '#' && h.charAt(1) !== '/') {
      var target = document.getElementById(h.slice(1));
      if (target && !target.closest('[hidden]')) { target.scrollIntoView(); return; }
      var L = legacy(h);
      if (L) { history.replaceState(null, '', L); h = L; }
    }
    var r = parse(h), p = r.parts;
    closePalette();
    if (!p.length) { showOpening(); return; }
    if (p[0] === 'read') withData(function () { showChapter(p[1] || CFG.firstChapter); });
    else if (p[0] === 'r') withData(function () { showResult(p[1], p[2], p[3]); });
    else if (p[0] === 'find') withData(function () { showFind(r.params.q || ''); });
    else if (p[0] === 'ideas') withData(function () { showIdeas(p[1], p[2]); });
    else if (p[0] === 'lean') withData(function () { showLean(p[1], r.params); });
    else if (p[0] === 'talk') showTalk(p[1]);
    else showOpening();
  }

  function showView(name) {
    var first = S.view === null;
    $$('#main > .view').forEach(function (v) { v.hidden = v.id !== 'v-' + name; });
    document.body.setAttribute('data-view', name);
    S.view = name;
    var key = parse(location.hash).parts;
    $$('.toc a[data-route]').forEach(function (a) {
      var rr = a.getAttribute('data-route');
      var on = rr === key.slice(0, 2).join('/') || ((rr === 'ideas' || rr === 'lean' || rr === 'talk' || rr === 'find') && rr === key[0]);
      a.classList.toggle('on', on);
      if (on) a.setAttribute('aria-current', 'page'); else a.removeAttribute('aria-current');
    });
    document.body.classList.remove('toc-open');
    $('.toc-toggle').setAttribute('aria-expanded', 'false');
    if (!first && !S.pendingAnchor) window.scrollTo(0, 0);
  }

  function barBottom() {
    var b = 0;
    ['.topbar', '.paperbar'].forEach(function (s) {
      var n = $(s);
      if (n && getComputedStyle(n).position !== 'static') b = Math.max(b, n.getBoundingClientRect().bottom);
    });
    return b;
  }
  function scrollToEl(el) {
    if (!el) return;
    var y = el.getBoundingClientRect().top + window.pageYOffset - barBottom() - 14;
    window.scrollTo(0, Math.max(0, y));
  }
  function flash(el) {
    if (!el) return;
    el.classList.remove('flash');
    void el.offsetWidth;
    el.classList.add('flash');
  }
  function afterRender() {
    if (S.pendingAnchor) {
      var el = document.getElementById(S.pendingAnchor);
      S.pendingAnchor = null;
      if (el) {
        var d = el.closest('details');
        if (d) d.open = true;
        scrollToEl(el);
        flash(el);
      }
    }
  }
  function initFigures(root) {
    if (!window.FLUPFigures) return;
    $$('[data-figure]', root).forEach(function (f) { window.FLUPFigures.render(f); });
  }

  // ------------------------------------------------------------------------------------------------ opening

  function showOpening() {
    showView('open');
    var v = $('#v-open');
    renderMath(v);
    initFigures(v);
    document.title = CFG.title || document.title;
  }

  // ------------------------------------------------------------------------------------------------ reading

  function showChapter(id) {
    var list = D.chapters, k = 0;
    if (!list.length) { showOpening(); return; }
    for (var j = 0; j < list.length; j++) if (list[j].id === id) k = j;
    var ch = list[k], v = $('#v-read');
    var dots = list.map(function (c, j) {
      return '<a class="pdot' + (j === k ? ' on' : '') + '" href="#/read/' + c.id + '" title="' + esc(strip(c.title)) +
        '" aria-label="Chapter ' + (j + 1) + ': ' + esc(strip(c.title)) + '"' + (j === k ? ' aria-current="step"' : '') + '></a>';
    }).join('');
    var prev = k > 0 ? '<a class="ch-prev" href="#/read/' + list[k - 1].id + '"><span>Previous</span>' + list[k - 1].title + '</a>'
      : '<a class="ch-prev" href="#/"><span>Back to</span>The question</a>';
    var next = k < list.length - 1 ? '<a class="ch-next" href="#/read/' + list[k + 1].id + '"><span>Next idea</span>' + list[k + 1].title + '</a>'
      : '<a class="ch-next" href="#/find"><span>Next</span>Every result of the paper</a>';
    v.innerHTML = '<header class="ch-head"><p class="kicker">Reading · ' + (k + 1) + ' of ' + list.length + '</p>' +
      '<h1 class="view-title ch-title">' + ch.title + '</h1>' + (ch.lead ? '<p class="ch-lead">' + ch.lead + '</p>' : '') +
      '<nav class="pdots" aria-label="Chapters">' + dots + '</nav></header>' +
      '<div class="ch-body">' + ch.html + '</div><nav class="ch-nav" aria-label="Chapters">' + prev + next + '</nav>';
    showView('read');
    renderMath(v, true);
    initFigures(v);
    document.title = strip(ch.title) + ' · ' + (CFG.title || '');
    afterRender();
  }

  // ------------------------------------------------------------------------------------------------ result pages

  function statusChip(r) {
    return r.status && r.status[1] ? '<span class="chip st-' + r.status[0] + '">' + esc(r.status[1]) + '</span>' : '';
  }
  function mapLinks(maps, cls) {
    var out = '';
    if (maps && maps.ideas) out += '<a class="' + cls + '" href="#/ideas/' + maps.ideas[0] + '/' + maps.ideas[1] + '" data-back>Ideas Map</a>';
    if (maps && maps.lean) out += '<a class="' + cls + '" href="#/lean/' + maps.lean[0] + '?b=' + maps.lean[1] + '" data-back>Lean Map</a>';
    return out;
  }
  function resLink(id) {
    var r = D.results[id];
    return r ? '<a class="x-item" href="#/r/' + id + '" data-x="item:' + id + '">' + esc(r.num) + '</a>' : esc(id);
  }
  function stepHtml(r, s) {
    var mv = D.mv[s.mv] || {};
    var ideas = (mv.ideas || []).map(function (x) { return '<li>' + x + '</li>'; }).join('');
    var more = (mv.intro || '') + (mv.statement || '') + (mv.sketch || '');
    var tree = r.tree;
    return '<li class="pstep' + (mv.kind === 'cited' ? ' cited' : '') + '" id="step-' + s.module + '">' +
      '<div class="pstep-h"><span class="chip">' + esc(s.chip) + '</span><h3 class="pstep-t">' + mv.title + '</h3>' +
      (mv.ref ? '<span class="pstep-ref">' + esc(mv.ref) + '</span>' : '') + '</div>' +
      (ideas ? '<ul class="pstep-ideas">' + ideas + '</ul>' : '') +
      '<div class="pstep-more">' +
      (more ? '<details><summary>More detail</summary><div class="dbody">' + more + '</div></details>' : '') +
      (mv.std ? '<details class="paper"><summary>The paper\'s text</summary><div class="dbody">' + mv.std + '</div></details>' : '') +
      (mv.study ? '<details class="study"><summary>Extended details</summary><div class="dbody">' + mv.study + '</div></details>' : '') +
      '</div><p class="pstep-maps"><a href="#/ideas/' + tree + '/' + s.module + '" data-back>Ideas Map</a>' +
      '<a href="#/lean/' + tree + '?b=' + s.module + '" data-back>Lean Map</a></p></li>';
  }
  function proofHtml(r) {
    if (r.steps && r.steps.length) {
      var apps = (r.apps || []).map(resLink).join(', ');
      return '<section class="r-sec r-proof" id="r-proof"><h2 class="r-h">The proof, step by step</h2>' +
        '<p class="r-hint">Each step shows its idea first. Open <em>More detail</em>, <em>The paper\'s text</em> or ' +
        '<em>Extended details</em> where you want to go further.</p><ol class="psteps">' +
        r.steps.map(function (s) { return stepHtml(r, s); }).join('') + '</ol>' +
        (apps ? '<aside class="appcall"><p class="app-k">Applications</p><p>' + apps + '</p></aside>' : '') + '</section>';
    }
    var mv = r.mv ? D.mv[r.mv] : null;
    var stepOf = (r.stepOf || []).map(function (x) {
      var t = D.results[x[0]];
      return '<a href="#/r/' + x[0] + '/step/' + r.module + '">' + esc(x[2] || 'a step') + ' of ' + esc(t ? t.num : x[0]) + '</a>';
    }).join(', ');
    return '<section class="r-sec r-proof" id="r-proof"><h2 class="r-h">Proof</h2>' +
      (r.proof ? '<details class="paper" id="r-proof-paper"><summary>The paper\'s proof</summary><div class="dbody">' + r.proof + '</div></details>'
        : '<p class="muted">The paper gives no separate proof of this item; its role is explained above.</p>') +
      (mv && mv.study ? '<details class="study"><summary>Extended details</summary><div class="dbody">' + mv.study + '</div></details>' : '') +
      (stepOf ? '<p class="r-stepof">Where it is used: ' + stepOf + '.</p>' : '') + '</section>';
  }
  function relHtml(r) {
    var uses = (r.uses || []).map(resLink).join(', '), used = (r.usedIn || []).map(resLink).join(', ');
    var lean = (r.decls || []).map(function (n) {
      return '<a class="lean-link" href="#/lean/' + ((r.maps && r.maps.lean && r.maps.lean[0]) || CFG.defaults.g) + '?n=' + encodeURIComponent(n) + '" data-back><code>' + esc(n) + '</code></a>';
    }).join(' ');
    if (!uses && !used && !lean) return '';
    return '<section class="r-sec r-rel"><h2 class="r-h">Connections</h2>' +
      (uses ? '<p><span class="rel-k">Uses</span> ' + uses + '</p>' : '') +
      (used ? '<p><span class="rel-k">Used in</span> ' + used + '</p>' : '') +
      (lean ? '<p><span class="rel-k">In Lean</span> ' + lean + '</p>' : '') + '</section>';
  }
  function showResult(id, sub, arg) {
    var r = D.results[id];
    if (!r) { showFind(id || ''); return; }
    var v = $('#v-result');
    var jump = '<nav class="r-jump" aria-label="On this page">' +
      (r.statement ? '<a href="#/r/' + id + '/statement">Statement</a>' : '') +
      (r.idea ? '<a href="#/r/' + id + '/idea">Idea</a>' : '') + '<a href="#/r/' + id + '/proof">Proof</a></nav>';
    v.innerHTML = '<article class="rpage fam-' + r.family + '">' +
      '<header class="r-head"><p class="kicker">' + esc(FAMILY[r.family] || '') + (r.section ? ' · §' + esc(r.section) : '') + '</p>' +
      '<h1 class="r-title"><span class="r-num">' + esc(r.num) + tagHtml(r) + '</span><span class="r-name">' + r.name + '</span></h1>' +
      '<p class="r-meta">' + statusChip(r) + (r.pdf ? '<a href="' + CFG.pdf + '#page=' + r.pdf + '" target="_blank" rel="noopener">PDF p. ' + r.pdf + ' ↗</a>' : '') +
      mapLinks(r.maps, '') + '</p>' + jump + '</header>' +
      (r.plain ? '<section class="r-sec r-plain" id="r-plain"><h2 class="r-h">In plain words</h2>' + r.plain + '</section>' : '') +
      (r.statement ? '<section class="r-sec r-statement" id="r-statement"><h2 class="r-h">Statement</h2><div class="thm">' + r.statement + '</div></section>' : '') +
      (r.idea ? '<section class="r-sec r-idea" id="r-idea"><h2 class="r-h">The main idea</h2>' + r.idea + '</section>' : '') +
      proofHtml(r) + relHtml(r) + '</article>';
    showView('result');
    renderMath(v, true);
    document.title = r.num + (r.tag ? ' (' + r.tag + ')' : '') + ' · ' + (CFG.title || '');
    if (sub === 'statement') scrollToEl($('#r-statement'));
    else if (sub === 'idea') scrollToEl($('#r-idea'));
    else if (sub === 'proof') {
      var d = $('#r-proof-paper');
      if (d) d.open = true;
      scrollToEl($('#r-proof'));
    } else if (sub === 'step' && arg) {
      var st = document.getElementById('step-' + arg);
      if (st) { scrollToEl(st); flash(st); }
    }
    afterRender();
  }

  // ------------------------------------------------------------------------------------------------ openings next to the passage

  function xContent(key) {
    var kind = key.split(':')[0], id = key.slice(kind.length + 1);
    if (kind === 'term') {
      var g = D.glossary[id];
      if (!g) return null;
      return { cls: 'x-' + g.kind, head: '<span class="x-kind">' + esc(g.kind === 'example' ? 'Example' : g.kind === 'explanation' ? 'Explanation' : 'Definition') +
        '</span><b class="x-term-t">' + g.term + '</b>', body: g.html };
    }
    if (kind === 'cite') {
      var c = D.bib[id];
      return c ? { cls: 'x-cite', head: '<span class="x-kind">Reference [' + c.n + ']</span><b class="x-term-t"></b>', body: '<p>' + c.html + '</p>' } : null;
    }
    var r = D.results[id];
    if (!r) return null;
    return { cls: 'x-result fam-' + r.family, head: '<span class="x-kind">' + esc(r.num) + tagHtml(r) + '</span><b class="x-term-t">' + r.name + '</b>',
      body: (r.plain || '') + (r.statement ? '<div class="thm">' + r.statement + '</div>' : '') +
        '<p class="x-more"><a href="#/r/' + id + '">The idea and the proof →</a></p>' };
  }
  function toggleX(btn) {
    if (btn._box && btn._box.parentNode) {
      btn._box.parentNode.removeChild(btn._box);
      btn._box = null;
      btn.setAttribute('aria-expanded', 'false');
      return;
    }
    var c = xContent(btn.getAttribute('data-x'));
    if (!c) return;
    var host = btn.closest('p, li, .tp, .thm, .x-body > *, td, .rplain, .fr') || btn.parentNode;
    var box = document.createElement('div');
    box.className = 'x-box ' + c.cls;
    box.setAttribute('role', 'note');
    box.innerHTML = '<div class="x-head">' + c.head + '<button type="button" class="x-close" aria-label="Close">×</button></div><div class="x-body">' + c.body + '</div>';
    var after = host;
    while (after.nextElementSibling && after.nextElementSibling.classList.contains('x-box')) after = after.nextElementSibling;
    after.parentNode.insertBefore(box, after.nextSibling);
    box._btn = btn;
    btn._box = box;
    btn.setAttribute('aria-expanded', 'true');
    renderMath(box, true);
  }

  // ------------------------------------------------------------------------------------------------ finding a result

  function search(q) {
    q = (q || '').trim().toLowerCase();
    var list = D.search;
    if (!q) return list.filter(function (e) { return e.family !== 'term'; });
    var bare = q.replace(/[()\s]/g, ''), toks = q.split(/\s+/), out = [];
    list.forEach(function (e, k) {
      var num = e.num.toLowerCase(), numBare = num.replace(/[()\s]/g, ''), score = 0;
      if (/^[a-z]?\d/.test(bare) && numBare.indexOf(bare) >= 0) score += 20 - Math.min(10, numBare.length - bare.length);
      if (toks.every(function (t) { return e.text.indexOf(t) >= 0 || num.indexOf(t) >= 0; })) {
        score += 2 + (strip(e.name).toLowerCase().indexOf(q) >= 0 ? 4 : 0);
      }
      if (score) out.push([score, k, e]);
    });
    out.sort(function (a, b) { return b[0] - a[0] || a[1] - b[1]; });
    return out.map(function (x) { return x[2]; });
  }
  function rowHtml(e, active) {
    if (e.family === 'term') {
      return '<button type="button" class="fr fr-term x-term' + (active ? ' active' : '') + '" data-x="' + e.id + '" role="option">' +
        '<span class="fr-num">Term</span><span class="fr-name">' + e.name + '</span></button>';
    }
    return '<a class="fr fam-' + e.family + (active ? ' active' : '') + '" href="#/r/' + e.id + '" role="option">' +
      '<span class="fr-num">' + esc(e.num) + tagHtml(e) + '</span><span class="fr-name">' + e.name + '</span></a>';
  }
  function showFind(q) {
    var v = $('#v-find'), input = $('#find-q', v);
    if (input.value !== q) input.value = q;
    drawFind(q);
    showView('find');
    if (!q) input.focus();
  }
  function drawFind(q) {
    var v = $('#v-find'), list = $('.find-list', v), res = search(q);
    if (q) {
      list.innerHTML = res.length ? '<div class="fl">' + res.map(function (e) { return rowHtml(e); }).join('') + '</div>'
        : '<p class="muted">Nothing matches “' + esc(q) + '”. Try a number such as 3.2 or a name such as Silvestre.</p>';
    } else {
      var groups = {}, order = [];
      res.forEach(function (e) {
        var s = (e.section || '').split('.')[0] || '—';
        if (!groups[s]) { groups[s] = []; order.push(s); }
        groups[s].push(e);
      });
      list.innerHTML = order.map(function (s) {
        var title = (D.sections && D.sections[s]) ? D.sections[s] : '';
        return '<section class="fg"><h2 class="fg-h">' + (s === '—' ? 'Other' : '§' + esc(s) + ' ' + title) + '</h2><div class="fl">' +
          groups[s].map(function (e) { return rowHtml(e); }).join('') + '</div></section>';
      }).join('');
    }
    renderMath(list, true);
  }

  // the search field of the opening and the palette (press / or Ctrl+K)
  function popList(input, pop) {
    var q = input.value, res = q.trim() ? search(q).slice(0, 8) : [];
    pop.hidden = !res.length;
    pop.innerHTML = res.map(function (e, k) { return rowHtml(e, k === 0); }).join('');
    renderMath(pop, true);
  }
  function moveActive(pop, d) {
    var rows = $$('.fr', pop), k = rows.findIndex(function (x) { return x.classList.contains('active'); });
    if (!rows.length) return;
    if (k >= 0) rows[k].classList.remove('active');
    k = (k + d + rows.length) % rows.length;
    rows[k].classList.add('active');
    rows[k].scrollIntoView({ block: 'nearest' });
  }
  function openActive(pop, input) {
    var a = $('.fr.active', pop) || $('.fr', pop);
    if (!a) { location.hash = '#/find?q=' + encodeURIComponent(input.value); return; }
    if (a.tagName === 'A') location.hash = a.getAttribute('href');
    else { location.hash = '#/find?q=' + encodeURIComponent(input.value); }
  }
  function openPalette() {
    withData(function () {
      var p = $('.palette'), input = $('.palette-input', p);
      p.hidden = false;
      document.body.classList.add('palette-open');
      input.value = '';
      popList(input, $('.palette-list', p));
      input.focus();
    });
  }
  function closePalette() {
    var p = $('.palette');
    if (p && !p.hidden) { p.hidden = true; document.body.classList.remove('palette-open'); }
  }

  // ------------------------------------------------------------------------------------------------ Ideas Map

  function treeChoices(sel, attr) {
    return CFG.settings.concat(CFG.extraTrees).map(function (s) {
      return '<button type="button" role="radio" class="seg" ' + attr + '="' + s.id + '" data-set="' + s.id + '" aria-checked="' +
        (s.id === sel) + '" title="' + esc(s.sub) + '"><span class="dot"></span>' + s.label + '</button>';
    }).join('');
  }
  function showIdeas(t, node) {
    t = D.ideas[t] ? t : (S.tree || CFG.defaults.g);
    showView('ideas');
    showBackbar('ideas');
    var v = $('#v-ideas'), pick = $('.tree-pick', v);
    pick.innerHTML = treeChoices(t, 'data-tree');
    renderMath(pick, true);
    if (S.tree !== t) drawTree(t);
    var T = D.ideas[t], has = T.nodes.some(function (n) { return n.id === node; });
    selectNode(has ? node : (T.nodes.some(function (n) { return n.id === 'root'; }) ? 'root' : T.nodes[0].id), !has);
    afterRender();
  }
  function drawTree(t) {
    S.tree = t;
    var v = $('#v-ideas'), T = D.ideas[t], grid = $('.tree-grid', v), maxCol = 1;
    T.nodes.forEach(function (n) { maxCol = Math.max(maxCol, n.col); });
    grid.style.gridTemplateColumns = 'repeat(' + maxCol + ', minmax(170px, 1fr))';
    grid.innerHTML = T.nodes.map(function (n) {
      return '<button type="button" class="tnode k-' + n.kind + '" data-node="' + n.id + '" style="grid-row:' + (n.row + 1) +
        ';grid-column:' + n.col + '"><span class="chip">' + esc(n.chip) + '</span><span class="tn-label">' + n.label + '</span>' +
        (n.sub ? '<span class="tn-sub">' + n.sub + '</span>' : '') + '</button>';
    }).join('');
    v.setAttribute('data-set', t);
    renderMath(grid, true);
    watchTree(v);
    scheduleEdges();
  }
  // the arrows follow the boxes: redraw them whenever the frame or a box changes size (fonts, formulas, scrollbar)
  var edgeRO = 'ResizeObserver' in window ? new ResizeObserver(function () { scheduleEdges(); }) : null, edgesQueued = false;
  function scheduleEdges() {
    if (edgesQueued) return;
    edgesQueued = true;
    requestAnimationFrame(function () { edgesQueued = false; drawEdges(); });
  }
  function watchTree(v) {
    if (!edgeRO) return;
    edgeRO.disconnect();
    edgeRO.observe($('.tree-frame', v));
    $$('.tnode', v).forEach(function (n) { edgeRO.observe(n); });
  }
  if (document.fonts && document.fonts.addEventListener) document.fonts.addEventListener('loadingdone', scheduleEdges);
  function drawEdges() {
    if (S.view !== 'ideas' || !S.tree) return;
    var v = $('#v-ideas'), frame = $('.tree-frame', v), svg = $('.tree-edges', v), fr = frame.getBoundingClientRect(), out = [];
    svg.setAttribute('width', frame.scrollWidth);
    svg.setAttribute('height', frame.scrollHeight);
    function box(id) {
      var n = $('.tnode[data-node="' + id + '"]', frame);
      if (!n) return null;
      var r = n.getBoundingClientRect();
      return { x: r.left - fr.left + frame.scrollLeft, y: r.top - fr.top, w: r.width, h: r.height };
    }
    D.ideas[S.tree].nodes.forEach(function (n) {
      (n.parents || []).forEach(function (p) {
        var a = box(p), b = box(n.id);
        if (!a || !b) return;
        var x1 = a.x + a.w / 2, y1 = a.y + a.h, x2 = b.x + b.w / 2, y2 = b.y, my = (y1 + y2) / 2;
        var on = S.node && (S.node === p || S.node === n.id);
        out.push('<path class="' + (on ? 'on' : '') + '" d="M' + x1 + ',' + y1 + ' C' + x1 + ',' + my + ' ' + x2 + ',' + my + ' ' + x2 + ',' + y2 + '"/>');
      });
    });
    svg.innerHTML = out.join('');
  }
  function selectNode(id, quiet) {
    var T = D.ideas[S.tree], n = null;
    T.nodes.forEach(function (x) { if (x.id === id) n = x; });
    if (!n) return;
    S.node = id;
    $$('#v-ideas .tnode').forEach(function (b) { b.classList.toggle('on', b.getAttribute('data-node') === id); });
    drawEdges();
    var mv = D.mv[n.mv] || {};
    var below = T.nodes.filter(function (x) { return (x.parents || []).indexOf(id) >= 0; });
    function links(list) {
      return list.map(function (x) {
        return '<button type="button" class="tn-ref" data-node="' + x.id + '"><span class="chip">' + esc(x.chip) + '</span> ' + x.label + '</button>';
      }).join('');
    }
    var above = T.nodes.filter(function (x) { return (n.parents || []).indexOf(x.id) >= 0; });
    var body = S.td === 'sum' ? (mv.statement || '') + (mv.sketch || '')
      : '<ul class="tp-ideas">' + (mv.ideas || []).map(function (x) { return '<li>' + x + '</li>'; }).join('') + '</ul>';
    var panel = $('#v-ideas .tree-panel');
    panel.innerHTML = '<p class="tp-chips"><span class="chip">' + esc(n.chip) + '</span></p><h2 class="tp-title">' + n.label + '</h2>' +
      (n.sub ? '<p class="tp-sub">' + n.sub + '</p>' : '') +
      '<div class="segs tp-switch" role="radiogroup" aria-label="Detail"><button type="button" role="radio" class="seg" data-td="ideas" aria-checked="' +
      (S.td !== 'sum') + '">Ideas</button><button type="button" role="radio" class="seg" data-td="sum" aria-checked="' + (S.td === 'sum') + '">Summary</button></div>' +
      '<div class="tp-body">' + body + '</div>' +
      (above.length ? '<div class="tp-rel"><span class="tp-k">Used in</span>' + links(above) + '</div>' : '') +
      (below.length ? '<div class="tp-rel"><span class="tp-k">Rests on</span>' + links(below) + '</div>' : '') +
      '<p class="tp-go"><a href="' + n.href + '">Read this step in the text →</a><a href="#/lean/' + S.tree + '?b=' + n.id + '">See it in the Lean Map →</a></p>';
    renderMath(panel, true);
    if (!quiet) history.replaceState(null, '', '#/ideas/' + S.tree + '/' + id);
  }

  // ------------------------------------------------------------------------------------------------ Lean Map

  function showLean(t, params) {
    showView('lean');
    showBackbar('lean');
    var p = Object.assign({}, params);
    if (t) p.t = t;
    if (window.FLUPLean) window.FLUPLean.show(p);
  }

  // the way back from a map to the passage of the text that led there
  function showBackbar(view) {
    var bar = $('#v-' + view + ' .backbar');
    if (!bar) return;
    var b = S.back;
    if (!b || !b.hash) { bar.hidden = true; return; }
    bar.innerHTML = '<a href="' + esc(b.hash) + '" data-return>← Back to ' + esc(b.label) + '</a>';
    bar.hidden = false;
  }
  function backLabel(anchor) {
    var v = $('#main > .view:not([hidden])');
    var num = v && $('.r-num', v), name = v && $('.r-name', v), title = v && $('.view-title', v);
    var label = num ? num.textContent.trim() : (title ? title.textContent : 'the text');
    var chip = anchor && anchor.querySelector('.chip');
    if (chip) label += ' · ' + chip.textContent.trim().replace(/^STEP/i, 'Step');
    else if (num && name) label += ' · ' + name.textContent.trim();
    label = label.replace(/\s+/g, ' ').trim();
    return label.length > 70 ? label.slice(0, 68) + '…' : label;
  }

  // ------------------------------------------------------------------------------------------------ seminar

  function loadDecks() {
    $$('.deck-iframe[data-src]').forEach(function (f) { if (!f.getAttribute('src')) f.setAttribute('src', f.getAttribute('data-src')); });
  }
  function whenLoaded(frame, fn) {
    var doc = null;
    try { doc = frame.contentDocument; } catch (e) { doc = null; }
    if (doc && doc.readyState === 'complete' && doc.getElementById('contents')) fn(doc);
    else frame.addEventListener('load', function () {
      try { fn(frame.contentDocument); } catch (e) { /* another origin: no jump */ }
    }, { once: true });
  }
  function jumpSlide(n) {
    var frame = $('.deck-iframe');
    if (!frame) return;
    $$('.note').forEach(function (x) { x.classList.toggle('on', Number(x.getAttribute('data-slide')) === n); });
    frame.scrollIntoView({ block: 'center' });
    whenLoaded(frame, function (doc) {
      if (!doc) return;
      var open = doc.getElementById('contents');
      if (!open) return;
      open.click();
      var t = doc.querySelectorAll('#jump-list .jump')[n - 1];
      if (t) t.click();
      else {
        var dialog = doc.getElementById('contents-dialog');
        if (dialog && dialog.open) dialog.close();
      }
    });
  }
  function showTalk(n) {
    showView('talk');
    loadDecks();
    renderMath($('#v-talk'));
    if (n) jumpSlide(Number(n));
  }

  // ------------------------------------------------------------------------------------------------ events

  document.addEventListener('click', function (e) {
    var t = e.target.closest('a, button');
    if (!t) return;
    if (t.matches('a[data-back]')) {
      var anchor = t.closest('[id]');
      S.back = { hash: location.hash || '#/', anchor: anchor && anchor.id !== 'main' ? anchor.id : '', label: backLabel(anchor) };
      try { sessionStorage.setItem('flup-back', JSON.stringify(S.back)); } catch (err) { /* ignore */ }
      return;
    }
    if (t.matches('a[data-return]')) { S.pendingAnchor = S.back && S.back.anchor; return; }
    if (t.matches('.x-close')) { var box = t.closest('.x-box'); if (box && box._btn) toggleX(box._btn); else if (box) box.remove(); return; }
    if (t.matches('a[href^="#ref-"]') && !(e.metaKey || e.ctrlKey || e.shiftKey)) {
      e.preventDefault();
      t.setAttribute('data-x', 'cite:' + t.getAttribute('href').slice(5));
      withData(function () { toggleX(t); });
      return;
    }
    if (t.matches('.x-term, .x-item') && !(e.metaKey || e.ctrlKey || e.shiftKey)) {
      e.preventDefault();
      withData(function () { toggleX(t); });
      return;
    }
    if (t.matches('.tree-pick .seg')) {
      $$('#v-ideas .tree-pick .seg').forEach(function (b) { b.setAttribute('aria-checked', b === t ? 'true' : 'false'); });
      S.node = null; drawTree(t.getAttribute('data-tree')); var T = D.ideas[S.tree];
      selectNode(T.nodes.some(function (n) { return n.id === 'root'; }) ? 'root' : T.nodes[0].id); return; }
    if (t.matches('.tnode, .tn-ref')) { selectNode(t.getAttribute('data-node')); return; }
    if (t.matches('.tp-switch .seg')) { S.td = t.getAttribute('data-td'); selectNode(S.node, true); return; }
    if (t.matches('[data-palette]')) { openPalette(); return; }
    if (t.matches('.toc-toggle')) {
      var open = !document.body.classList.contains('toc-open');
      document.body.classList.toggle('toc-open', open);
      t.setAttribute('aria-expanded', open ? 'true' : 'false');
      return;
    }
    if (t.matches('button.jump')) { var n = Number(t.getAttribute('data-n')); jumpSlide(n); history.replaceState(null, '', '#/talk/' + n); return; }
    if (t.matches('[data-fullscreen]')) {
      var f = document.getElementById(t.getAttribute('data-fullscreen'));
      loadDecks();
      if (f && f.requestFullscreen) f.requestFullscreen();
      return;
    }
    if (t.closest('.palette') && t.matches('.fr')) { closePalette(); }
  });

  // the search field of the opening
  var heroForm = $('form[data-find]');
  if (heroForm) {
    var heroInput = $('input', heroForm), heroPop = $('.find-pop', heroForm);
    heroInput.addEventListener('input', function () { withData(function () { popList(heroInput, heroPop); }); });
    heroInput.addEventListener('keydown', function (e) {
      if (e.key === 'ArrowDown') { e.preventDefault(); moveActive(heroPop, 1); }
      else if (e.key === 'ArrowUp') { e.preventDefault(); moveActive(heroPop, -1); }
      else if (e.key === 'Escape') { heroPop.hidden = true; }
    });
    heroForm.addEventListener('submit', function (e) {
      e.preventDefault();
      withData(function () {
        if (heroInput.value.trim() && !heroPop.hidden) openActive(heroPop, heroInput);
        else location.hash = '#/find' + (heroInput.value.trim() ? '?q=' + encodeURIComponent(heroInput.value.trim()) : '');
      });
    });
    document.addEventListener('click', function (e) { if (!heroForm.contains(e.target)) heroPop.hidden = true; });
  }
  var findForm = $('form[data-find-page]');
  if (findForm) {
    var fq = $('input', findForm);
    fq.addEventListener('input', function () {
      withData(function () { drawFind(fq.value); history.replaceState(null, '', '#/find' + (fq.value ? '?q=' + encodeURIComponent(fq.value) : '')); });
    });
    findForm.addEventListener('submit', function (e) {
      e.preventDefault();
      var a = $('#v-find .fr');
      if (a && a.tagName === 'A') location.hash = a.getAttribute('href');
    });
  }
  var pal = $('.palette');
  if (pal) {
    var pin = $('.palette-input', pal), plist = $('.palette-list', pal);
    pin.addEventListener('input', function () { popList(pin, plist); });
    pin.addEventListener('keydown', function (e) {
      if (e.key === 'ArrowDown') { e.preventDefault(); moveActive(plist, 1); }
      else if (e.key === 'ArrowUp') { e.preventDefault(); moveActive(plist, -1); }
      else if (e.key === 'Enter') { e.preventDefault(); closePalette(); openActive(plist, pin); }
      else if (e.key === 'Escape') { closePalette(); }
    });
    pal.addEventListener('click', function (e) { if (e.target === pal) closePalette(); });
  }

  document.addEventListener('keydown', function (e) {
    var typing = /^(INPUT|TEXTAREA|SELECT)$/.test((e.target.tagName || '')) || e.target.isContentEditable;
    if ((e.key === '/' && !typing) || ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'k')) { e.preventDefault(); openPalette(); return; }
    if (e.key === 'Escape') {
      var open = $$('.x-box');
      if (open.length && !typing) { var last = open[open.length - 1]; if (last._btn) { toggleX(last._btn); last._btn && last._btn.focus && last._btn.focus(); } else last.remove(); }
      return;
    }
    // one idea at a time: the arrow keys turn the chapters of the reading
    if (S.view === 'read' && !typing && !e.metaKey && !e.ctrlKey && !e.altKey && (e.key === 'ArrowRight' || e.key === 'ArrowLeft')) {
      var a = $(e.key === 'ArrowRight' ? '.ch-next' : '.ch-prev');
      if (a) { e.preventDefault(); location.hash = a.getAttribute('href'); }
    }
    // arrow keys inside radio groups
    if (['ArrowRight', 'ArrowLeft', 'ArrowDown', 'ArrowUp'].indexOf(e.key) >= 0) {
      var group = e.target.closest && e.target.closest('[role="radiogroup"]');
      if (!group || group.classList.contains('lean-pick')) return;
      var items = $$('[role="radio"]', group), k = items.indexOf(e.target);
      if (k < 0) return;
      e.preventDefault();
      var nx = items[(k + (e.key === 'ArrowRight' || e.key === 'ArrowDown' ? 1 : items.length - 1)) % items.length];
      nx.focus();
      nx.click();
    }
  });

  window.addEventListener('hashchange', route);
  window.addEventListener('resize', function () { if (S.view === 'ideas') scheduleEdges(); });

  window.FLUPApp = {
    renderMath: renderMath,
    currentView: function () { return S.view; },
    stepHref: function (tree, module) {
      if (CFG.settingItem[tree]) return '#/r/' + CFG.settingItem[tree] + '/step/' + module;
      var home = D && D.moduleHome[module];
      return home ? '#/r/' + home : '#/find';
    }
  };

  CFG.title = document.title;
  if (document.readyState === 'complete') route(); else document.addEventListener('DOMContentLoaded', route);
})();
