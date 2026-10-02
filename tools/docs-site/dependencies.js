/* Copyright (c) 2026 the Nonadditivity project contributors.
   All rights reserved. See COPYRIGHT.md for licensing and attribution. */
(() => {
  "use strict";
  const explorer = document.getElementById("dependency-explorer");
  if (!explorer) return;
  const nodes = window.HOLEVO_DEPENDENCIES || [];
  const root = document.body.dataset.root || "";
  const field = document.getElementById("dependency-search");
  const suggestions = document.getElementById("dependency-suggestions");
  const direction = document.getElementById("dependency-direction");
  const kind = document.getElementById("dependency-kind");
  const depth = document.getElementById("dependency-depth");
  const graph = document.getElementById("dependency-graph");
  const status = document.getElementById("dependency-status");
  const focusText = document.getElementById("dependency-focus");
  const list = document.getElementById("dependency-neighbors");
  const more = document.getElementById("dependency-more");
  const byName = new Map(nodes.map((node, i) => [node.name, i]));
  const byHash = new Map(nodes.map((node, i) => [node.url.split("/").pop().replace(/\.html$/, ""), i]));
  const reverse = {type: nodes.map(() => []), value: nodes.map(() => [])};
  nodes.forEach((node, i) => {
    for (const reference of node.type) reverse.type[reference].push(i);
    for (const reference of node.value) reverse.value[reference].push(i);
  });
  let focus = byName.get(explorer.dataset.focus) || 0;
  let listLimit = 50;
  function refs(i) {
    const source = direction.value === "users" ? {type: reverse.type[i], value: reverse.value[i]} : nodes[i];
    return (kind.value === "all" ? [...new Set([...source.type, ...source.value])] : source[kind.value]).slice().sort((a, b) => nodes[a].name.localeCompare(nodes[b].name));
  }
  function focusOn(i) {
    focus = i;
    field.value = nodes[i].name;
    suggestions.replaceChildren();
    const hash = nodes[i].url.split("/").pop().replace(/\.html$/, "");
    if (location.hash.slice(1) !== hash) location.hash = hash;
    listLimit = 50;
    render();
  }
  function svgElement(tag, attributes = {}) {
    const element = document.createElementNS("http://www.w3.org/2000/svg", tag);
    for (const [key, value] of Object.entries(attributes)) element.setAttribute(key, String(value));
    return element;
  }
  function draw() {
    const maxDepth = Number(depth.value);
    const levels = [[focus]];
    const visible = new Set([focus]);
    let truncated = false;
    for (let level = 0; level < maxDepth; level++) {
      const candidates = [...new Set(levels[level].flatMap(refs))].filter(i => !visible.has(i));
      // Prefer ordinary names without hiding private/internal constants from the graph.
      candidates.sort((a, b) => Number(nodes[a].internal) - Number(nodes[b].internal) || nodes[a].name.localeCompare(nodes[b].name));
      const next = candidates.slice(0, 4);
      if (candidates.length > next.length) truncated = true;
      if (!next.length) break;
      next.forEach(i => visible.add(i));
      levels.push(next);
    }
    const width = 1120;
    const height = levels.length * 118 + 24;
    const svg = svgElement("svg", {viewBox: `0 0 ${width} ${height}`, role: "group", "aria-label": "Bounded graph of direct Lean project-constant references"});
    const title = svgElement("title");
    title.textContent = "Arrows point from a declaration to a constant it references. Select a node to focus its neighborhood.";
    svg.appendChild(title);
    const defs = svgElement("defs");
    const marker = svgElement("marker", {id: "reference-arrow", markerWidth: 8, markerHeight: 8, refX: 7, refY: 4, orient: "auto", markerUnits: "strokeWidth"});
    marker.appendChild(svgElement("path", {d: "M0,0 L8,4 L0,8 z", fill: "#72967e"}));
    defs.appendChild(marker);
    svg.appendChild(defs);
    const positions = new Map();
    levels.forEach((level, n) => level.forEach((i, column) => positions.set(i, {x: width * (column + 0.5) / level.length, y: n * 118 + 54})));
    const seenEdges = new Set();
    for (const i of visible) {
      for (const j of refs(i)) {
        if (!visible.has(j) || i === j) continue;
        const from = direction.value === "users" ? j : i;
        const to = direction.value === "users" ? i : j;
        const key = from + ":" + to;
        if (seenEdges.has(key)) continue;
        seenEdges.add(key);
        const a = positions.get(from), b = positions.get(to);
        const sign = b.y >= a.y ? 1 : -1;
        svg.appendChild(svgElement("path", {d: `M${a.x},${a.y + sign * 27} L${b.x},${b.y - sign * 32}`, fill: "none", stroke: "#72967e", "stroke-width": 1.5, "marker-end": "url(#reference-arrow)"}));
      }
    }
    for (const i of visible) {
      const p = positions.get(i);
      const boxWidth = Math.min(264, width / levels.find(level => level.includes(i)).length - 14);
      const group = svgElement("g", {tabindex: 0, role: "button", "aria-label": "Focus " + nodes[i].name, class: "graph-node"});
      const tooltip = svgElement("title");
      tooltip.textContent = nodes[i].name + "\n" + nodes[i].kind + " · " + nodes[i].module;
      group.appendChild(tooltip);
      group.appendChild(svgElement("rect", {x: p.x - boxWidth / 2, y: p.y - 27, width: boxWidth, height: 54, rx: 5, fill: i === focus ? "#286449" : "#fffefb", stroke: "#72967e"}));
      const short = nodes[i].name.startsWith("Nonadditivity.") ? nodes[i].name.slice(14) : nodes[i].name;
      const label = svgElement("text", {x: p.x, y: p.y - 2, "text-anchor": "middle", fill: i === focus ? "white" : "#25342c", "font-size": 11, "font-family": "ui-monospace, monospace"});
      label.textContent = short.length > 32 ? short.slice(0, 29) + "…" : short;
      group.appendChild(label);
      const detail = svgElement("text", {x: p.x, y: p.y + 16, "text-anchor": "middle", fill: i === focus ? "#dcebd9" : "#626f67", "font-size": 10});
      detail.textContent = nodes[i].kind + (nodes[i].internal ? " · internal/detail/private" : "");
      group.appendChild(detail);
      group.addEventListener("click", () => focusOn(i));
      group.addEventListener("keydown", event => { if (event.key === "Enter" || event.key === " ") { event.preventDefault(); focusOn(i); } });
      svg.appendChild(group);
    }
    graph.replaceChildren(svg);
    status.textContent = visible.size + " visible constants, " + seenEdges.size + " visible direct edges; depth " + maxDepth + ". " + (truncated ? "Some branches are omitted from the diagram. Follow the complete direct-neighbor list below." : "No branch was omitted within this depth.");
  }
  function render() {
    focusText.replaceChildren();
    const label = document.createElement("span");
    label.textContent = "Selected: ";
    const link = document.createElement("a");
    link.href = root + nodes[focus].url;
    const code = document.createElement("code");
    code.textContent = nodes[focus].name;
    link.appendChild(code);
    focusText.append(label, link);
    draw();
    const neighbors = refs(focus);
    list.replaceChildren();
    const summary = document.createElement("p");
    summary.className = "small muted";
    summary.textContent = neighbors.length.toLocaleString() + " direct project neighbors; showing " + Math.min(listLimit, neighbors.length) + ".";
    list.appendChild(summary);
    for (const i of neighbors.slice(0, listLimit)) {
      const row = document.createElement("div");
      row.className = "neighbor-row";
      const button = document.createElement("button");
      button.type = "button";
      button.className = "neighbor-focus";
      button.textContent = "Focus";
      button.setAttribute("aria-label", "Focus " + nodes[i].name);
      button.addEventListener("click", () => focusOn(i));
      const a = document.createElement("a");
      a.href = root + nodes[i].url;
      const name = document.createElement("code");
      name.textContent = nodes[i].name;
      a.appendChild(name);
      row.append(button, a);
      list.appendChild(row);
    }
    more.hidden = listLimit >= neighbors.length;
  }
  field.addEventListener("input", () => {
    suggestions.replaceChildren();
    const words = field.value.toLowerCase().trim().split(/\s+/).filter(Boolean);
    if (!words.length) return;
    const matches = nodes.map((node, i) => i).filter(i => words.every(word => (nodes[i].name + " " + nodes[i].module).toLowerCase().includes(word)));
    for (const i of matches.slice(0, 8)) {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "dependency-suggestion";
      button.textContent = nodes[i].name;
      button.addEventListener("click", () => focusOn(i));
      suggestions.appendChild(button);
    }
    if (!matches.length) {
      const p = document.createElement("p");
      p.className = "small muted";
      p.textContent = "No matching project constant.";
      suggestions.appendChild(p);
    }
  });
  field.addEventListener("keydown", event => { if (event.key === "Enter") { const first = suggestions.querySelector("button"); if (first) { event.preventDefault(); first.click(); } } });
  for (const control of [direction, kind, depth]) control.addEventListener("change", () => { listLimit = 50; render(); });
  more.addEventListener("click", () => { listLimit += 50; render(); });
  document.getElementById("dependency-collapse").addEventListener("click", () => { depth.value = "1"; render(); });
  window.addEventListener("hashchange", () => { const i = byHash.get(location.hash.slice(1)); if (i !== undefined && i !== focus) { focus = i; field.value = nodes[i].name; listLimit = 50; render(); } });
  const initial = byHash.get(location.hash.slice(1));
  if (initial !== undefined) focus = initial;
  field.value = nodes[focus].name;
  render();
})();
