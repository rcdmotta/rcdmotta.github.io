// Light and dark mode.
// By default the site follows the visitor's device: the colours in style.css switch to
// the dark ones when the device is in dark mode. The moon/sun button in the top bar picks
// the other mode; the browser remembers that choice until the visitor switches back to
// the mode their device uses, and then the site follows the device again.
// Each page loads this file at the top of <head> (without "defer"), so a remembered
// choice is applied before the page is drawn and the page never flashes in the wrong mode.
(function () {
  var root = document.documentElement;
  var deviceDark = window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)');

  function deviceMode() {
    return deviceDark && deviceDark.matches ? 'dark' : 'light';
  }

  function currentMode() {
    var chosen = root.getAttribute('data-theme');
    return chosen === 'light' || chosen === 'dark' ? chosen : deviceMode();
  }

  // Apply a remembered choice right away.
  try {
    var saved = localStorage.getItem('theme');
    if (saved === 'light' || saved === 'dark') root.setAttribute('data-theme', saved);
  } catch (e) { /* storage blocked: just follow the device */ }

  document.addEventListener('DOMContentLoaded', function () {
    var button = document.querySelector('.theme-toggle');
    if (!button) return;

    button.addEventListener('click', function () {
      var next = currentMode() === 'dark' ? 'light' : 'dark';
      var followDevice = next === deviceMode();

      root.classList.add('theme-transition');
      window.setTimeout(function () { root.classList.remove('theme-transition'); }, 400);

      if (followDevice) root.removeAttribute('data-theme');
      else root.setAttribute('data-theme', next);

      try {
        if (followDevice) localStorage.removeItem('theme');
        else localStorage.setItem('theme', next);
      } catch (e) { /* storage blocked: the choice lasts until the visitor leaves the page */ }
    });
  });
})();
