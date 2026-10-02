/* Copyright (c) 2026 the Nonadditivity project contributors.
   All rights reserved. See COPYRIGHT.md for licensing and attribution. */
(() => {
  "use strict";
  const root = document.body.dataset.root || "";
  const input = document.getElementById("site-search");
  const results = document.getElementById("search-results");
  const data = window.HOLEVO_SEARCH || [];
  const internal = document.getElementById("search-internal");
  function addMessage(message) {
    const p = document.createElement("div");
    p.className = "search-message";
    p.textContent = message;
    results.appendChild(p);
  }
  if (input && results) {
    function search() {
      const words = input.value.trim().toLowerCase().split(/\s+/).filter(Boolean);
      results.replaceChildren();
      results.hidden = words.length === 0;
      if (!words.length) return;
      const query = input.value.trim().toLowerCase();
      const matches = data.filter(item => (!item.internal || (internal && internal.checked)) && words.every(word => item.search.includes(word))).sort((a, b) => {
        const score = item => item.title.toLowerCase() === query ? 0 : words.every(word => item.title.toLowerCase().includes(word)) ? (item.reader ? 1 : 2) : item.reader ? 3 : 4;
        return score(a) - score(b) || a.title.localeCompare(b.title);
      });
      if (!matches.length) { addMessage("No matching concept, result or Lean declaration. Try another term or include internal constants."); return; }
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
    }
    input.addEventListener("input", search);
    if (internal) internal.addEventListener("change", search);
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
  const catalog = document.getElementById("declaration-catalog");
  if (catalog) {
    const field = document.getElementById("declaration-search");
    const includeInternal = document.getElementById("declaration-internal");
    const kind = document.getElementById("declaration-kind");
    const status = document.getElementById("declaration-status");
    const more = document.getElementById("declaration-more");
    const declarations = data.filter(item => item.declaration);
    let limit = 100;
    function render(reset) {
      if (reset) limit = 100;
      const words = field.value.toLowerCase().trim().split(/\s+/).filter(Boolean);
      const matches = declarations.filter(item => (!item.internal || includeInternal.checked) && (!kind.value || item.kind === kind.value) && words.every(word => item.search.includes(word)));
      catalog.replaceChildren();
      for (const item of matches.slice(0, limit)) {
        const row = document.createElement("div");
        row.className = "declaration-row";
        const a = document.createElement("a");
        a.href = root + item.url;
        const code = document.createElement("code");
        code.textContent = item.title;
        a.appendChild(code);
        const detail = document.createElement("span");
        detail.className = "small muted";
        detail.textContent = item.detail + (item.internal ? " · internal/detail/private" : "");
        row.append(a, detail);
        catalog.appendChild(row);
      }
      status.textContent = matches.length.toLocaleString() + " matching constants; showing " + Math.min(limit, matches.length).toLocaleString() + ".";
      more.hidden = limit >= matches.length;
    }
    field.addEventListener("input", () => render(true));
    includeInternal.addEventListener("change", () => render(true));
    kind.addEventListener("change", () => render(true));
    more.addEventListener("click", () => { limit += 100; render(false); });
    render(true);
  }
  document.querySelectorAll(".full-type").forEach(details => {
    let started = false;
    details.addEventListener("toggle", async () => {
      if (!details.open || started) return;
      started = true;
      const status = details.querySelector(".full-type-status");
      if (typeof DecompressionStream !== "function") {
        status.textContent = "This browser cannot decode gzip locally. Download the complete compressed artifact and decompress it with gzip or Python.";
        return;
      }
      status.textContent = "Decoding the exact type artifact locally; only a bounded preview will be rendered…";
      try {
        const encoded = JSON.parse(details.querySelector(".full-type-payload").textContent);
        const binary = atob(encoded);
        const packed = Uint8Array.from(binary, character => character.charCodeAt(0));
        const stream = new Blob([packed]).stream().pipeThrough(new DecompressionStream("gzip"));
        const reader = stream.getReader();
        const decoder = new TextDecoder("utf-8", {fatal: true});
        const chunks = [];
        let bytes = 0, previewCount = 0, preview = "", truncated = false;
        function addPreview(text) {
          if (!text) return;
          if (previewCount >= 64000) { truncated = true; return; }
          const characters = [];
          const available = 64000 - previewCount;
          for (const character of text) {
            if (characters.length >= available) { truncated = true; break; }
            characters.push(character);
          }
          preview += characters.join("");
          previewCount += characters.length;
        }
        while (true) {
          const {done, value} = await reader.read();
          if (done) break;
          bytes += value.byteLength;
          if (bytes > Number(details.dataset.size)) throw new Error("Decoded byte count exceeds the recorded size");
          chunks.push(value);
          addPreview(decoder.decode(value, {stream: true}));
        }
        addPreview(decoder.decode());
        if (bytes !== Number(details.dataset.size)) throw new Error("Decoded byte count differs from the recorded size");
        const complete = new Blob(chunks, {type: details.dataset.suffix === ".expr.json" ? "application/json;charset=utf-8" : "text/plain;charset=utf-8"});
        let verifiedHash = false;
        if (globalThis.crypto && crypto.subtle) {
          const digest = await crypto.subtle.digest("SHA-256", await complete.arrayBuffer());
          const hex = Array.from(new Uint8Array(digest), byte => byte.toString(16).padStart(2, "0")).join("");
          if (hex !== details.dataset.sha256) throw new Error("Decoded SHA-256 differs from the recorded hash");
          verifiedHash = true;
        }
        const pre = details.querySelector(".full-type-preview");
        pre.querySelector("code").textContent = preview;
        pre.hidden = false;
        const link = document.createElement("a");
        link.href = URL.createObjectURL(complete);
        link.download = details.dataset.filename;
        link.textContent = " · Download the complete artifact (" + (details.dataset.suffix || ".txt") + ")";
        details.querySelector(".full-type-download").appendChild(link);
        status.textContent = (truncated ? "Preview truncated to the first 64,000 characters; both download links contain the entire artifact. " : "The complete artifact is shown. ") + (verifiedHash ? "UTF-8, byte count and SHA-256 verified locally." : "UTF-8 and byte count verified locally; the SHA-256 is shown above.");
      } catch (error) {
        status.textContent = "Local artifact decoding failed: " + error.message + ". The complete compressed download remains available.";
      }
    });
  });
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
