/* Copyright (c) 2026 the Nonadditivity project contributors.
   All rights reserved. See COPYRIGHT.md for licensing and attribution. */
(() => {
  "use strict";
  const root = document.body.dataset.root || "";
  const input = document.getElementById("site-search");
  const results = document.getElementById("search-results");
  const data = window.HOLEVO_SEARCH || [];
  function addMessage(message) {
    const p = document.createElement("div");
    p.className = "search-message";
    p.textContent = message;
    results.appendChild(p);
  }
  if (input && results) {
    input.addEventListener("input", () => {
      const words = input.value.trim().toLowerCase().split(/\s+/).filter(Boolean);
      results.replaceChildren();
      results.hidden = words.length === 0;
      if (!words.length) return;
      const matches = data.filter(item => words.every(word => item.search.includes(word)));
      if (!matches.length) { addMessage("No matching result or module."); return; }
      matches.slice(0, 30).forEach(item => {
        const a = document.createElement("a");
        a.className = "search-result";
        a.href = root + item.url;
        const title = document.createElement("b");
        title.textContent = item.title;
        const detail = document.createElement("span");
        detail.textContent = item.detail;
        a.append(title, detail);
        results.appendChild(a);
      });
      if (matches.length > 30) addMessage("Showing the first 30 of " + matches.length + " matches. Refine your search.");
    });
    input.addEventListener("keydown", event => {
      if (event.key === "Escape") { results.hidden = true; input.blur(); }
      if (event.key === "Enter") {
        const first = results.querySelector("a");
        if (first && !results.hidden) { event.preventDefault(); first.click(); }
      }
    });
    document.addEventListener("click", event => {
      if (!event.target.closest(".search-wrap")) results.hidden = true;
    });
    input.addEventListener("focus", () => { if (input.value.trim()) results.hidden = false; });
  }
  document.querySelectorAll("[data-filter]").forEach(field => {
    const items = document.querySelectorAll(field.dataset.filter);
    field.addEventListener("input", () => {
      const query = field.value.trim().toLowerCase();
      let count = 0;
      items.forEach(item => {
        const visible = (item.dataset.search || item.textContent).toLowerCase().includes(query);
        item.classList.toggle("hidden", !visible);
        if (visible) count++;
      });
      const status = document.getElementById(field.dataset.status || "");
      if (status) status.textContent = count + " matching entries";
    });
  });
  document.querySelectorAll(".copy").forEach(button => {
    button.addEventListener("click", async () => {
      const text = button.parentElement.querySelector("pre code").textContent;
      let copied = false;
      try {
        if (navigator.clipboard && window.isSecureContext) {
          await navigator.clipboard.writeText(text);
          copied = true;
        }
      } catch (_) { /* The offline fallback is used below. */ }
      if (!copied) {
        const box = document.createElement("textarea");
        box.value = text;
        box.style.position = "fixed";
        box.style.opacity = "0";
        document.body.appendChild(box);
        box.select();
        try { copied = document.execCommand("copy"); } catch (_) { copied = false; }
        box.remove();
      }
      const original = button.textContent;
      button.textContent = copied ? "Copied" : "Select and copy";
      if (!copied) {
        const selection = window.getSelection();
        const range = document.createRange();
        range.selectNodeContents(button.parentElement.querySelector("pre code"));
        selection.removeAllRanges(); selection.addRange(range);
      }
      window.setTimeout(() => { button.textContent = original; }, 1800);
    });
  });
})();
