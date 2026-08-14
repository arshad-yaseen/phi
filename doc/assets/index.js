(function () {
  'use strict';

  const keywords = new Set([
    'and', 'break', 'continue', 'defer', 'else', 'extern', 'fn', 'if',
    'import', 'in', 'is', 'let', 'loop', 'match', 'not', 'or', 'pub',
    'return', 'type', 'var',
  ]);

  const primitives = new Set([
    'i8', 'i16', 'i32', 'i64', 'u8', 'u16', 'u32', 'u64', 'f32', 'f64',
    'bool', 'str',
  ]);

  const constants = new Set(['true', 'false', 'none']);

  const token = new RegExp(
    '\\/\\/[^\\n]*' +
      '|"(?:\\\\.|[^"\\\\\\n])*"?' +
      "|'(?:\\\\.|[^'\\\\\\n])*'?" +
      '|@[A-Za-z_][A-Za-z0-9_]*' +
      '|[A-Za-z_][A-Za-z0-9_]*' +
      '|0[xob][0-9a-fA-F_]+(?:\\.[0-9a-fA-F_]+)?(?:[pP][+-]?[0-9]+)?' +
      '|[0-9][0-9_]*(?:\\.[0-9_]+)?(?:[eE][+-]?[0-9]+)?',
    'g'
  );

  function classify(text, next) {
    if (text.startsWith('//')) return 'comment';
    if (text[0] === '"' || text[0] === "'") return 'string';
    if (text[0] === '@') return 'builtin';
    if (text[0] >= '0' && text[0] <= '9') return 'number';
    if (keywords.has(text)) return 'keyword';
    if (primitives.has(text)) return 'type';
    if (constants.has(text)) return 'constant';
    if (text[0] >= 'A' && text[0] <= 'Z') return 'type';
    if (next === '(') return 'function';
    return null;
  }

  function span(cls, text) {
    const node = document.createElement('span');
    node.className = cls;
    node.textContent = text;
    return node;
  }

  function paintSource(code) {
    const text = code.textContent;
    const out = document.createDocumentFragment();
    let last = 0;
    let match;
    token.lastIndex = 0;
    while ((match = token.exec(text)) !== null) {
      if (match.index > last) {
        out.appendChild(document.createTextNode(text.slice(last, match.index)));
      }
      const cls = classify(match[0], text[token.lastIndex]);
      if (cls === null) {
        out.appendChild(document.createTextNode(match[0]));
      } else {
        out.appendChild(span(cls, match[0]));
      }
      last = token.lastIndex;
    }
    if (last < text.length) {
      out.appendChild(document.createTextNode(text.slice(last)));
    }
    code.textContent = '';
    code.appendChild(out);
  }

  function paintConsole(code) {
    const lines = code.textContent.split('\n');
    const out = document.createDocumentFragment();
    lines.forEach(function (line, at) {
      if (line.startsWith('$ ')) {
        out.appendChild(span('prompt', '$'));
        out.appendChild(document.createTextNode(line.slice(1)));
      } else {
        out.appendChild(span('output', line));
      }
      if (at + 1 < lines.length) out.appendChild(document.createTextNode('\n'));
    });
    code.textContent = '';
    code.appendChild(out);
  }

  document.querySelectorAll('pre > code:not([class])').forEach(function (code) {
    if (code.textContent.startsWith('$ ')) {
      paintConsole(code);
    } else {
      paintSource(code);
    }
  });

  const line = 88;

  function spy() {
    const links = Array.from(document.querySelectorAll('.page-toc a[href^="#"]'));
    const sections = links
      .map(function (link) {
        return {
          link: link,
          heading: document.getElementById(decodeURIComponent(link.hash.slice(1))),
        };
      })
      .filter(function (section) {
        return section.heading !== null;
      });
    if (sections.length === 0) return;

    const wide = window.matchMedia('(min-width: 1280px)');
    let current = null;
    let queued = false;

    function update() {
      queued = false;
      if (!wide.matches) return;

      let active = sections[0];
      sections.forEach(function (section) {
        if (section.heading.getBoundingClientRect().top <= line) active = section;
      });

      const doc = document.documentElement;
      if (window.innerHeight + window.scrollY >= doc.scrollHeight - 2) {
        active = sections[sections.length - 1];
      }

      if (active === current) return;
      if (current !== null) current.link.classList.remove('active');
      active.link.classList.add('active');
      current = active;
    }

    function schedule() {
      if (queued) return;
      queued = true;
      requestAnimationFrame(update);
    }

    window.addEventListener('scroll', schedule, { passive: true });
    window.addEventListener('resize', schedule, { passive: true });
    wide.addEventListener('change', schedule);
    update();
  }

  spy();

  function stored() {
    try {
      return localStorage.getItem('theme');
    } catch (e) {
      return null;
    }
  }

  function theme() {
    const root = document.documentElement;
    const button = document.getElementById('theme');
    if (button === null) return;

    const system = window.matchMedia('(prefers-color-scheme: dark)');

    function apply(name) {
      root.dataset.theme = name;
      button.setAttribute(
        'aria-label',
        name === 'dark' ? 'Switch to light theme' : 'Switch to dark theme'
      );
    }

    apply(stored() || (system.matches ? 'dark' : 'light'));

    button.addEventListener('click', function () {
      const next = root.dataset.theme === 'dark' ? 'light' : 'dark';
      try {
        localStorage.setItem('theme', next);
      } catch (e) {}
      apply(next);
    });

    system.addEventListener('change', function () {
      if (stored() === null) apply(system.matches ? 'dark' : 'light');
    });
  }

  theme();
})();
