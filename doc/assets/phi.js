// Colours the Phi blocks, which are the code blocks with no language, because
// Zine only knows the languages it ships a grammar for and Phi is not one.
// The classes are the ones the served highlighter emits, so one palette in
// style.css covers both.
(function () {
  "use strict";

  var KEYWORDS = new Set([
    "and", "break", "continue", "defer", "else", "extern", "fn", "if",
    "import", "in", "is", "let", "loop", "match", "not", "or", "pub",
    "return", "type", "var",
  ]);

  // spelled by the compiler, not declared anywhere a program can shadow
  var TYPES = new Set([
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64",
  ]);

  // std.prelude, visible in every file
  var PRELUDE_TYPES = new Set(["bool", "str"]);
  var PRELUDE_VALUES = new Set(["none", "true", "false"]);

  var TOKEN = new RegExp([
    "(\\/\\/[^\\n]*)",                              // comment
    "(\"(?:\\\\.|[^\"\\\\])*\")",                   // string
    "('(?:\\\\.|[^'\\\\])*')",                      // character
    "(\\\\\\\\[^\\n]*)",                            // a multi-line string's line
    "(@[A-Za-z_]\\w*)",                             // builtin
    "(0[xX][0-9a-fA-F_]+|\\d[\\d_]*(?:\\.\\d[\\d_]*)?)", // number
    "([A-Za-z_]\\w*)",                              // name
    "(\\.\\.|[+\\-*/%=<>!&|^~]+)",                  // operator
    "([{}()\\[\\].,:])",                            // punctuation
  ].join("|"), "g");

  function nameClass(word, source, start, end) {
    if (KEYWORDS.has(word)) return "keyword";
    if (TYPES.has(word) || PRELUDE_TYPES.has(word)) return "type_builtin";
    if (PRELUDE_VALUES.has(word)) return "constant_builtin";
    if (source[end] === "(") return "function";
    // a member reaches through one dot, where '0..len' is a range through two
    if (source[start - 1] === "." && source[start - 2] !== ".") return "property";
    // a type is capitalised, which is the convention the reference follows
    if (/^[A-Z]/.test(word)) return "type";
    return null;
  }

  function tokenClass(match, source) {
    if (match[1] !== undefined) return "comment";
    if (match[2] !== undefined || match[3] !== undefined) return "string";
    if (match[4] !== undefined) return "string";
    if (match[5] !== undefined) return "function";
    if (match[6] !== undefined) return "number";
    if (match[7] !== undefined) {
      return nameClass(match[7], source, match.index, match.index + match[7].length);
    }
    if (match[8] !== undefined) return "operator";
    return "punctuation";
  }

  function escape(text) {
    return text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }

  function highlight(source) {
    var out = "";
    var last = 0;
    var match;
    TOKEN.lastIndex = 0;
    while ((match = TOKEN.exec(source)) !== null) {
      var class_name = tokenClass(match, source);
      if (class_name === null) continue;
      out += escape(source.slice(last, match.index));
      out += '<span class="' + class_name + '">' + escape(match[0]) + "</span>";
      last = match.index + match[0].length;
    }
    return out + escape(source.slice(last));
  }

  document.querySelectorAll("pre > code:not([class])").forEach(function (block) {
    block.innerHTML = highlight(block.textContent);
    block.className = "phi";
  });
})();
