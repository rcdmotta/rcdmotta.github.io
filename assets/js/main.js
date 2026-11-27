// Phone menu: the menu button opens and closes the side drawer (screens narrower than 768px).
(function () {
  var bar = document.querySelector('.topbar');
  var button = document.querySelector('.menu-button');
  var backdrop = document.querySelector('.backdrop');
  if (!bar || !button) return;

  function setOpen(open) {
    bar.classList.toggle('menu-open', open);
    button.setAttribute('aria-expanded', open ? 'true' : 'false');
    button.setAttribute('aria-label', open ? 'Close menu' : 'Open menu');
  }

  button.addEventListener('click', function () {
    setOpen(!bar.classList.contains('menu-open'));
  });

  if (backdrop) {
    backdrop.addEventListener('click', function () { setOpen(false); });
  }

  document.addEventListener('keydown', function (event) {
    if (event.key === 'Escape') setOpen(false);
  });

  // Close the drawer if the window becomes wide enough for the normal menu.
  var wide = window.matchMedia('(min-width: 768px)');
  var onChange = function (e) { if (e.matches) setOpen(false); };
  if (wide.addEventListener) wide.addEventListener('change', onChange);
  else if (wide.addListener) wide.addListener(onChange);
})();
