// Usage: FLUPFigures.render(el) draws the figure named by el.dataset.figure (here only "threshold").
// The figure of the opening, in dimension one, drawn for the model sets of the paper (§1.2).
//   Λ, the zeros of f, runs from dense to sparse through the logarithmic sets {±(log n)^a}, with a from 1/2 up to
//     infinity, then through the power sets {±n^α}, 0 < α < 1, up to the lattice ℤ.
//   M, the zeros of (−Δ)^s f, runs through the sets of the examples after Theorem 1.1: {±(log n)^b} with b > 1, then
//     {±n^β} with 0 < β < 1. The lattice ℤ enters only through the lattice pair Λ = M = ℤ of Theorem 1.3.
// On this domain every pair is decided by the paper, so the phase map has no undecided region:
//   a ≤ 1: uniqueness, Theorem 1.1 (i) on X_{s,σ}(ℝ) when M is logarithmic (β = b > 1), Theorem 1.1 (ii) on 𝒮(ℝ)
//     when M is a power set (α = β);
//   a > 1, power sets or ℤ: both sets are ρ-separated with ρ < 1, Theorem 1.2 (every s > 0); a real-analytic f when
//     both sets are at the power scale, Theorem 1.4 (s = 1/2); a band-limited f on the lattice pair, Theorem 1.3.
// The logarithmic part of each axis is compactified (a ↦ (a − 1/2)/(a + 1/2), b ↦ 1 − 1/b), so that it reaches a = ∞
// and b = ∞ where the power sets begin.
(function () {
  'use strict';
  var R = 5, W = 760, H = 132, X0 = 24, X1 = W - 24, YL = 40, YM = 96, YA = 68, NMAX = 6000;
  var TJ = 0.6, YJ = 0.55, AMAX = 60;               // where the power sets begin on each axis; largest exponent shown
  var PX0 = 54, PY0 = 12, PS = 236;                 // phase map: square of side PS at (PX0, PY0) in a 300 × 290 box
  var TAG = { 'thm-1.1-i': ['UP', 'uniqueness'], 'thm-1.1-ii': ['UP', 'uniqueness'], 'thm-1.2': ['NUP', 'non-uniqueness'],
    'thm-1.3': ['NUP, entire', 'non-uniqueness'], 'thm-1.4': ['NUP, real-analytic', 'non-uniqueness'] };

  function round(v, k) { return Math.round(v / k) * k; }
  function nice(a) {                                // exponents of the logarithmic sets, rounded for display
    var r = a < 2 ? round(a, 0.05) : a < 5 ? round(a, 0.1) : a < 20 ? round(a, 0.5) : Math.round(a);
    return Math.min(AMAX, Math.abs(r - 1) < 0.03 ? 1 : r);
  }
  function fmt(v) { return String(Math.round(v * 100) / 100); }
  // the two axes: t for Λ, u for M, both in [0, 1]
  function fromT(t) {
    t = Math.max(0, Math.min(1, t));
    if (t < TJ) { var v = Math.min(t / TJ, 0.983); return { f: 'log', v: Math.max(0.5, nice(0.5 * (1 + v) / (1 - v))) }; }
    var al = (t - TJ) / (1 - TJ);
    return al > 0.975 ? { f: 'lat', v: 1 } : { f: 'pow', v: Math.min(0.95, Math.max(0.05, round(al, 0.05))) };
  }
  function toT(S) {
    if (S.f === 'lat') return 1;
    if (S.f === 'pow') return TJ + (1 - TJ) * S.v;
    return TJ * (S.v - 0.5) / (S.v + 0.5);
  }
  function fromU(u) {
    u = Math.max(0, Math.min(1, u));
    if (u < YJ) { var v = Math.min(u / YJ, 0.983); return { f: 'log', v: Math.max(1.05, nice(1 / (1 - v))) }; }
    return { f: 'pow', v: Math.min(0.95, Math.max(0.05, round((u - YJ) / (1 - YJ), 0.05))) };
  }
  function toU(S) {
    if (S.f === 'lat') return 1;
    if (S.f === 'pow') return YJ + (1 - YJ) * S.v;
    return YJ * (1 - 1 / S.v);
  }

  // ---------------------------------------------------------------------------------------------- the point sets
  function sx(x) { return X0 + (x + R) / (2 * R) * (X1 - X0); }
  function sample(S) {
    var xs = [0];
    if (S.f === 'lat') { for (var k = 1; k <= R; k++) xs.push(k, -k); return { xs: xs, band: null }; }
    for (var n = S.f === 'log' ? 2 : 1; n <= NMAX; n++) {
      var x = S.f === 'log' ? Math.pow(Math.log(n), S.v) : Math.pow(n, S.v);
      if (x > R) return { xs: xs, band: null };
      xs.push(x, -x);
    }
    var xb = S.f === 'log' ? Math.pow(Math.log(NMAX + 1), S.v) : Math.pow(NMAX + 1, S.v);
    return { xs: xs, band: xb < R ? xb : null };
  }
  function count(S) {
    if (S.f === 'lat') return 2 * R + 1;
    var N = S.f === 'log' ? Math.exp(Math.pow(R, 1 / S.v)) : Math.pow(R, 1 / S.v);
    return S.f === 'log' ? 2 * Math.floor(N) - 1 : 2 * Math.floor(N) + 1;
  }
  function texNum(n) {
    if (n < 1e6) return String(n);
    var e = Math.floor(Math.log10(n));
    return '\\approx ' + (Math.round(n / Math.pow(10, e) * 10) / 10) + '\\cdot 10^{' + e + '}';
  }
  function setTex(S, name) {
    if (S.f === 'lat') return '\\(' + name + '=\\mathbb Z\\)';
    if (S.f === 'pow') return '\\(' + name + '=\\{\\pm n^{' + fmt(S.v) + '}\\}\\)';
    return '\\(' + name + '=\\{\\pm' + (S.v === 1 ? '\\log n' : '(\\log n)^{' + fmt(S.v) + '}') + '\\}\\)';
  }
  function gapTex(S) {
    if (S.f === 'lat') return 'with gaps equal to \\(1\\)';
    if (S.f === 'log') return 'with gaps of about \\(e^{-|x|' + (S.v === 1 ? '' : '^{' + fmt(1 / S.v) + '}') + '}\\) near \\(x\\)';
    return 'with gaps of about \\(|x|^{' + fmt(1 - 1 / S.v) + '}\\) near \\(x\\)';
  }
  function dots(xs, y, cls) {
    var px_ = xs.map(sx).sort(function (a, b) { return a - b; }), out = [], last = -1e9;
    px_.forEach(function (p) {
      if (p - last >= 0.7) { out.push('<circle class="' + cls + '" cx="' + p.toFixed(1) + '" cy="' + y + '" r="2.6"/>'); last = p; }
    });
    return out.join('');
  }
  function band(b, y, cls) {
    if (b == null) return '';
    var w = (sx(R) - sx(b)).toFixed(1);
    return '<rect class="' + cls + '" x="' + sx(b).toFixed(1) + '" y="' + (y - 3) + '" width="' + w + '" height="6" rx="3"/>' +
      '<rect class="' + cls + '" x="' + sx(-R).toFixed(1) + '" y="' + (y - 3) + '" width="' + w + '" height="6" rx="3"/>';
  }
  function axis() {
    var out = '<line class="ax" x1="' + X0 + '" y1="' + YA + '" x2="' + X1 + '" y2="' + YA + '"/>';
    for (var k = -R; k <= R; k++) {
      var x = sx(k).toFixed(1);
      out += '<line class="tick" x1="' + x + '" y1="' + (YA - 4) + '" x2="' + x + '" y2="' + (YA + 4) + '"/>' +
        '<text class="tl" x="' + x + '" y="' + (YA + 18) + '" text-anchor="middle">' + (k < 0 ? '−' + (-k) : k) + '</text>';
    }
    return out;
  }

  // ---------------------------------------------------------------------------------------------- what the paper proves
  function ref(id, num) {
    var t = TAG[id];
    return '<a href="#/r/' + id + '">' + num + '</a>' + (t ? ' <span class="rtag fam-' + t[1] + '">' + t[0] + '</span>' : '');
  }
  function verdict(L, M) {
    if (L.f === 'log' && L.v <= 1) {
      var why = '\\(\\Lambda\\) has positive lower density at the logarithmic scale \\(\\Phi_{1,1}\\), and \\(M\\) at the scale ';
      return { cls: 'is-unique', html: '<p class="v-k">Uniqueness pair</p>' + (M.f === 'log'
        ? '<p>For \\(0&lt;s&lt;1\\), every \\(f\\in X_{s,\\sigma}(\\mathbb R)\\) with \\(f|_\\Lambda=0\\) and \\((-\\Delta)^s f|_M=0\\) vanishes identically.</p>' +
          '<ul><li>' + ref('thm-1.1-i', 'Theorem 1.1 (i)') + ' applies, since ' + why + '\\(\\Phi_{\\beta,1}\\) with \\(\\beta=' + fmt(M.v) + '&gt;1\\).</li></ul>'
        : '<p>For \\(0&lt;s&lt;1\\), every \\(f\\in\\mathcal S(\\mathbb R)\\) with \\(f|_\\Lambda=0\\) and \\((-\\Delta)^s f|_M=0\\) vanishes identically.</p>' +
          '<ul><li>' + ref('thm-1.1-ii', 'Theorem 1.1 (ii)') + ' applies, since ' + why + '\\(G_\\alpha\\) with \\(\\alpha=' + fmt(M.v) + '&lt;1\\).</li></ul>') };
    }
    var n = [];
    if (L.f === 'lat' && M.f === 'lat') {
      n.push('<li>' + ref('thm-1.3', 'Theorem 1.3') + ' gives a band-limited \\(f\\), the restriction of an entire function of exponential type, for every \\(s&gt;0\\).</li>');
    }
    n.push('<li>' + ref('thm-1.2', 'Theorem 1.2') + ' gives \\(f\\) in the class \\(\\mathcal S^{p,q}_s(\\mathbb R)\\) of Schwartz functions, for every \\(s&gt;0\\), since both sets are \\(\\rho\\)-separated with \\(\\rho&lt;1\\).</li>');
    if (L.f !== 'log' && M.f !== 'log') {
      n.push('<li>' + ref('thm-1.4', 'Theorem 1.4') + ' gives a real-analytic \\(f\\) for \\(s=\\tfrac12\\), since both sets have finite upper density at a power scale.</li>');
    }
    return { cls: 'is-nonunique', html: '<p class="v-k">Non-uniqueness pair</p><p>Some nonzero \\(f\\) vanishes on \\(\\Lambda\\) while \\((-\\Delta)^s f\\) vanishes on \\(M\\).</p><ul>' + n.join('') + '</ul>' };
  }

  // ---------------------------------------------------------------------------------------------- the phase map
  var TA1 = toT({ f: 'log', v: 1 });                // the threshold a = 1
  function px(t) { return PX0 + PS * t; }
  function py(u) { return PY0 + PS * (1 - u); }
  function rect(t0, t1, u0, u1, cls) {
    return '<rect class="' + cls + '" x="' + px(t0).toFixed(1) + '" y="' + py(u1).toFixed(1) + '" width="' + (PS * (t1 - t0)).toFixed(1) +
      '" height="' + (PS * (u1 - u0)).toFixed(1) + '"/>';
  }
  function mapSvg() {
    var s = rect(0, TA1, 0, 1, 'r-u') + rect(TA1, 1, 0, 1, 'r-n') + rect(TJ, 1, YJ, 1, 'r-a');
    s += '<line class="sepl" x1="' + px(TJ) + '" y1="' + py(0) + '" x2="' + px(TJ) + '" y2="' + py(1) + '"/>' +
      '<line class="sepl" x1="' + px(0) + '" y1="' + py(YJ) + '" x2="' + px(1) + '" y2="' + py(YJ) + '"/>';
    s += '<line class="thr" x1="' + px(TA1) + '" y1="' + py(0) + '" x2="' + px(TA1) + '" y2="' + py(1) + '"/>';
    s += '<rect class="frame" x="' + PX0 + '" y="' + PY0 + '" width="' + PS + '" height="' + PS + '"/>';
    s += '<text class="rl rl-u" x="' + px(TA1 / 2) + '" y="' + py(0.3) + '" text-anchor="middle">UP</text>' +
      '<text class="rl rl-n" x="' + px((TA1 + TJ) / 2) + '" y="' + py(0.3) + '" text-anchor="middle">NUP</text>' +
      '<text class="rl rl-a" x="' + px((TJ + 1) / 2) + '" y="' + py(0.8) + '" text-anchor="middle">real-analytic</text>';
    s += '<g class="star" role="button" tabindex="0" aria-label="The lattice pair: Λ = M = ℤ"><title>The lattice pair Λ = M = ℤ (Theorem 1.3)</title>' +
      '<circle class="star-bg" cx="' + px(1) + '" cy="' + py(1) + '" r="11"/>' +
      '<text class="rl-b" x="' + px(1) + '" y="' + (py(1) + 4.5) + '" text-anchor="middle">★</text></g>';
    s += '<circle class="pick" r="7" cx="0" cy="0"/>';
    return s;
  }
  function tick(cls, pos, tex) {
    return '<span class="pt ' + cls + '" style="' + (cls === 'pt-x' ? 'left:' + (px(pos) / 300 * 100).toFixed(2) : 'top:' + (py(pos) / 290 * 100).toFixed(2)) +
      '%">\\(' + tex + '\\)</span>';
  }
  function ticksHtml() {
    return tick('pt-x', 0, 'a=\\tfrac12') + tick('pt-x', TA1, 'a=1') + tick('pt-x', toT({ f: 'log', v: 2 }), '2') +
      tick('pt-x', TJ, 'a\\to\\infty') + tick('pt-x', TJ + (1 - TJ) / 2, 'n^{1/2}') + tick('pt-x', 1, '\\mathbb Z') +
      tick('pt-y', 0, 'b\\downarrow 1') + tick('pt-y', toU({ f: 'log', v: 2 }), 'b=2') + tick('pt-y', YJ, 'b\\to\\infty') +
      tick('pt-y', YJ + (1 - YJ) / 2, 'n^{1/2}') + tick('pt-y', 1, '\\beta\\uparrow 1');
  }

  // ---------------------------------------------------------------------------------------------- the figure
  function rowHtml(key, who) {
    var fams = key === 'L' ? [['log', '\\((\\log n)^{a}\\)'], ['pow', '\\(n^{\\alpha}\\)'], ['lat', '\\(\\mathbb Z\\)']]
      : [['log', '\\((\\log n)^{b}\\)'], ['pow', '\\(n^{\\beta}\\)'], ['lat', '\\(\\mathbb Z\\)']];
    fams = fams.map(function (f) {
      return '<button type="button" role="radio" class="seg" data-row="' + key + '" data-fam="' + f[0] + '" aria-checked="false"' +
        (key === 'M' && f[0] === 'lat' ? ' title="The lattice pair Λ = M = ℤ (Theorem 1.3)"' : '') + '>' + f[1] + '</button>';
    }).join('');
    return '<div class="ctl ctl-' + (key === 'L' ? 'l' : 'm') + '"><span class="ctl-t"><span class="sw sw-' + (key === 'L' ? 'l' : 'm') +
      '"></span>Zeros of ' + who + '</span><span class="segs fam" role="radiogroup" aria-label="Family">' + fams + '</span>' +
      '<span class="ctl-r"><input type="range" min="0" max="1" step="0.002" data-k="' + (key === 'L' ? 'a' : 'b') +
      '" aria-label="From dense to sparse"><output class="ctl-v"></output></span></div>';
  }
  var uid = 0;
  function render(el) {
    if (el.__fig || el.getAttribute('data-figure') !== 'threshold') return;
    el.__fig = true;
    uid++;
    var S = { L: { f: 'log', v: 1 }, M: { f: 'log', v: 2 } };
    var cap = el.querySelector('figcaption');
    var box = document.createElement('div');
    box.className = 'fig-wrap';
    box.innerHTML = '<div class="fig-ctl">' + rowHtml('L', '\\(f\\)') + rowHtml('M', '\\((-\\Delta)^s f\\)') + '</div>' +
      '<svg class="fig-svg" viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="The points of Λ above the line and of M below it, on [−5, 5]."></svg>' +
      '<div class="fig-legend"></div>' +
      '<div class="fig-bottom"><div class="pmap"><svg class="pmap-svg" viewBox="0 0 300 290" role="img" aria-label="Map of the pairs: Λ from dense to sparse horizontally, M vertically.">' +
      mapSvg() + '</svg><div class="pmap-ticks">' + ticksHtml() + '</div>' +
      '<p class="pmap-cap">\\(\\Lambda\\) sparser \\(\\rightarrow\\) · \\(M\\) sparser \\(\\uparrow\\) · drag the point<br>★ the lattice pair \\(\\Lambda=M=\\mathbb Z\\)</p></div>' +
      '<div class="fig-verdict" aria-live="polite"></div></div>';
    el.insertBefore(box, cap || null);
    var svg = box.querySelector('.fig-svg'), legend = box.querySelector('.fig-legend'), verdictEl = box.querySelector('.fig-verdict');
    var map = box.querySelector('.pmap-svg'), pick = map.querySelector('.pick'), star = map.querySelector('.star');
    var inputs = { L: box.querySelector('[data-k="a"]'), M: box.querySelector('[data-k="b"]') };
    function math(node) { if (window.FLUPApp) window.FLUPApp.renderMath(node, true); }
    function q(sel) { return Array.prototype.slice.call(box.querySelectorAll(sel)); }
    // M is the lattice only together with Λ (Theorem 1.3); leaving the lattice pair moves M to the nearest power set
    function setL(T) { S.L = T; if (S.M.f === 'lat' && T.f !== 'lat') S.M = { f: 'pow', v: 0.95 }; }
    function lattice() { S.L = { f: 'lat', v: 1 }; S.M = { f: 'lat', v: 1 }; }

    function update() {
      ['L', 'M'].forEach(function (key) {
        var T = S[key];
        inputs[key].value = key === 'L' ? toT(T) : toU(T);
        var out = inputs[key].parentNode.querySelector('.ctl-v');
        out.innerHTML = T.f === 'lat' ? '\\(\\mathbb Z\\)' : '\\(' + (T.f === 'log' ? (key === 'L' ? 'a' : 'b') : (key === 'L' ? '\\alpha' : '\\beta')) + '=' + fmt(T.v) + '\\)';
        inputs[key].setAttribute('aria-valuetext', T.f === 'lat' ? 'the lattice' : (T.f === 'log' ? 'logarithmic set, exponent ' : 'power set, exponent ') + fmt(T.v));
        q('.seg[data-row="' + key + '"]').forEach(function (b) { b.setAttribute('aria-checked', b.getAttribute('data-fam') === T.f ? 'true' : 'false'); });
      });
      var a = sample(S.L), b = sample(S.M);
      svg.innerHTML = axis() + band(a.band, YL, 'band-l') + band(b.band, YM, 'band-m') + dots(a.xs, YL, 'pt-l') + dots(b.xs, YM, 'pt-m');
      legend.innerHTML = '<p><span class="sw sw-l"></span>' + setTex(S.L, '\\Lambda') + ' has \\(' + texNum(count(S.L)) + '\\) points in \\([-5,5]\\), ' + gapTex(S.L) + '.</p>' +
        '<p><span class="sw sw-m"></span>' + setTex(S.M, 'M') + ' has \\(' + texNum(count(S.M)) + '\\) points in \\([-5,5]\\), ' + gapTex(S.M) + '.</p>';
      pick.setAttribute('cx', px(toT(S.L)).toFixed(1));
      pick.setAttribute('cy', py(toU(S.M)).toFixed(1));
      star.classList.toggle('on', S.M.f === 'lat');
      var v = verdict(S.L, S.M);
      box.classList.remove('is-unique', 'is-nonunique');
      box.classList.add(v.cls);
      verdictEl.innerHTML = v.html;
      math(box.querySelector('.fig-ctl'));
      math(legend);
      math(verdictEl);
    }
    box.addEventListener('click', function (e) {
      var t = e.target.closest('.seg[data-fam]');
      if (!t) return;
      var key = t.getAttribute('data-row'), f = t.getAttribute('data-fam');
      if (f === 'lat' && key === 'M') lattice();
      else if (key === 'L') setL(f === 'lat' ? { f: 'lat', v: 1 } : f === 'pow' ? { f: 'pow', v: 0.5 } : { f: 'log', v: 1 });
      else S.M = f === 'pow' ? { f: 'pow', v: 0.5 } : { f: 'log', v: 2 };
      update();
    });
    inputs.L.addEventListener('input', function () { setL(fromT(Number(inputs.L.value))); update(); });
    inputs.M.addEventListener('input', function () { S.M = fromU(Number(inputs.M.value)); update(); });
    function starGo(e) { e.stopPropagation(); lattice(); update(); }
    star.addEventListener('pointerdown', starGo);
    star.addEventListener('keydown', function (e) { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); starGo(e); } });
    // drag the point on the map; the corner is the lattice pair
    var dragging = false;
    function moveTo(e) {
      var r = map.getBoundingClientRect(), k = 300 / r.width;
      var t = ((e.clientX - r.left) * k - PX0) / PS, u = 1 - ((e.clientY - r.top) * k - PY0) / PS;
      if (t > 0.975 && u > 0.975) lattice();
      else { setL(fromT(t)); S.M = fromU(u); }
      update();
    }
    map.addEventListener('pointerdown', function (e) {
      dragging = true;
      try { map.setPointerCapture(e.pointerId); } catch (err) { /* synthetic events have no pointer to capture */ }
      moveTo(e);
    });
    map.addEventListener('pointermove', function (e) { if (dragging) moveTo(e); });
    map.addEventListener('pointerup', function () { dragging = false; });
    map.addEventListener('pointercancel', function () { dragging = false; });
    math(box.querySelector('.pmap-ticks'));
    math(box.querySelector('.pmap-cap'));
    update();
  }

  window.FLUPFigures = { render: render };
})();
