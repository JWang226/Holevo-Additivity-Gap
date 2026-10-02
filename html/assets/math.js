/* Copyright (c) 2026 the Nonadditivity project contributors.
   All rights reserved. See COPYRIGHT.md for licensing and attribution. */
(() => {
  "use strict";
  function typeset() {
    if (!window.katex) return;
    document.querySelectorAll(".math-inline, .math-display").forEach(node => {
      try {
        window.katex.render(node.textContent, node, {
          displayMode: node.classList.contains("math-display"),
          throwOnError: true, trust: false, strict: "error",
          output: "htmlAndMathml"
        });
      } catch (error) {
        node.classList.add("math-error");
        console.error("Could not typeset a mathematical expression", error);
      }
    });
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", typeset);
  else typeset();
})();
