/* Copyright (c) 2026 the Nonadditivity project contributors.
   All rights reserved. See COPYRIGHT.md for licensing and attribution. */
(() => {
  "use strict";

  const normalize = (value) => String(value || "")
    .normalize("NFKD")
    .replace(/[\u0300-\u036f]/g, "")
    .toLowerCase()
    .replace(/\s+/g, " ")
    .trim();

  function initialize() {
    const section = document.getElementById("manuscript-correspondence");
    if (!section) return;

    const controls = section.querySelector("#correspondence-controls");
    const query = section.querySelector("#correspondence-query");
    const status = section.querySelector("#correspondence-status");
    const reset = section.querySelector("#correspondence-reset");
    if (!controls || !query || !status || !reset) return;

    const count = section.querySelector("#correspondence-count");
    const empty = section.querySelector("#correspondence-empty");
    const rows = Array.from(section.querySelectorAll("[data-correspondence-row]"), (element) => ({
      element,
      search: normalize(element.dataset.search || element.textContent),
      status: element.dataset.proofStatus || "",
    }));

    function filter() {
      const tokens = normalize(query.value).split(" ").filter(Boolean);
      const selectedStatus = status.value || "all";
      let visible = 0;

      for (const row of rows) {
        const matches = (selectedStatus === "all" || row.status === selectedStatus)
          && tokens.every((token) => row.search.includes(token));
        row.element.hidden = !matches;
        if (matches) visible += 1;
      }

      if (count) {
        const noun = rows.length === 1 ? "record" : "records";
        count.textContent = !tokens.length && selectedStatus === "all"
          ? `${rows.length} correspondence ${noun}`
          : `${visible} of ${rows.length} correspondence ${noun}`;
      }
      if (empty) empty.hidden = visible !== 0;
    }

    query.addEventListener("input", filter);
    status.addEventListener("change", filter);
    reset.addEventListener("click", (event) => {
      event.preventDefault();
      query.value = "";
      status.value = "all";
      filter();
      query.focus();
    });

    controls.hidden = false;
    filter();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initialize, { once: true });
  } else {
    initialize();
  }
})();
