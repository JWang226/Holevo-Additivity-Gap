/* Copyright (c) 2026 the Nonadditivity project contributors.
   All rights reserved. See COPYRIGHT.md for licensing and attribution. */
(() => {
  "use strict";
  const explorer = document.getElementById("dependency-explorer");
  if (!explorer) return;
  const nodes = window.HOLEVO_DEPENDENCIES || [];
  const proof = window.HOLEVO_PROOF_GRAPH || {nodes: [], presets: []};
  const root = document.body.dataset.root || "";
  const get = id => document.getElementById(id);
  const field = get("dependency-search"), suggestions = get("dependency-suggestions");
  const direction = get("dependency-direction"), kind = get("dependency-kind"), depth = get("dependency-depth");
  const helpers = get("dependency-helpers"), graph = get("dependency-graph"), status = get("dependency-status");
  const focusText = get("dependency-focus"), list = get("dependency-neighbors"), more = get("dependency-more");
  const presetSelect = get("proof-preset"), proofMap = get("proof-map"), proofDetail = get("proof-detail");
  const proofStatus = get("proof-overview-status");
  const tabs = {overview: get("dependency-overview-tab"), references: get("dependency-references-tab")};
  const panels = {overview: get("dependency-overview-panel"), references: get("dependency-references-panel")};
  const byName = new Map(nodes.map((node, i) => [node.name, i]));
  const declarationHash = node => String(node.url || "").split("/").pop().replace(/\.html$/, "");
  const byHash = new Map(nodes.map((node, i) => [declarationHash(node), i]));
  const proofById = new Map((proof.nodes || []).map(node => [node.id, node]));
  const proofByIndex = new Map((proof.nodes || []).map(node => [node.index, node]));
  const presets = (proof.presets || []).filter(preset => Array.isArray(preset.node_ids) && preset.node_ids.length);
  const reverse = {type: nodes.map(() => []), value: nodes.map(() => [])};
  const validIndex = i => Number.isInteger(i) && i >= 0 && i < nodes.length;
  nodes.forEach((node, i) => {
    for (const relation of ["type", "value"]) {
      for (const reference of node[relation] || []) if (validIndex(reference)) reverse[relation][reference].push(i);
    }
  });
  let focus = byName.get(explorer.dataset.focus) ?? 0;
  let listLimit = 50;
  let mode = presets.length ? "overview" : "references";
  let activePreset = presets[0];
  let selectedProof = activePreset ? activePreset.root : undefined;
  let searchMatches = [], searchActive = -1;
  const graphLimit = 20, pageSize = 50;

  function element(tag, className, text) {
    const result = document.createElement(tag);
    if (className) result.className = className;
    if (text !== undefined) result.textContent = text;
    return result;
  }
  function link(url, text, className) {
    const result = element("a", className, text);
    result.href = root + url;
    return result;
  }
  function button(text, callback, className) {
    const result = element("button", className, text);
    result.type = "button";
    result.addEventListener("click", callback);
    return result;
  }
  function svgElement(tag, attributes = {}) {
    const result = document.createElementNS("http://www.w3.org/2000/svg", tag);
    for (const [key, value] of Object.entries(attributes)) result.setAttribute(key, String(value));
    return result;
  }
  function labelFor(node) { return node.label || node.name || node.id || "Declaration"; }
  function rank(i) {
    const node = nodes[i];
    return node.curated ? 0 : node.kind === "theorem" ? 1 : ["def", "definition", "opaque"].includes(node.kind) ? 2 : 3;
  }
  function compare(a, b) {
    return rank(a) - rank(b) || labelFor(nodes[a]).localeCompare(labelFor(nodes[b])) || nodes[a].name.localeCompare(nodes[b].name);
  }
  function allRefs(i) {
    const source = direction.value === "users" ? {type: reverse.type[i], value: reverse.value[i]} : nodes[i];
    const references = kind.value === "all" ? [...(source.type || []), ...(source.value || [])] : source[kind.value] || [];
    return [...new Set(references)].filter(validIndex).sort(compare);
  }
  function refs(i) { return allRefs(i).filter(j => (helpers && helpers.checked) || !nodes[j].internal); }
  function setHash(hash, nextMode) {
    const state = {dependencyMode: nextMode, dependencyPreset: activePreset && activePreset.id};
    if (location.hash.slice(1) === hash) history.replaceState(state, "", location.href);
    else history.pushState(state, "", "#" + hash);
  }
  function setMode(nextMode) {
    mode = nextMode === "overview" && presets.length ? "overview" : "references";
    for (const name of ["overview", "references"]) {
      if (tabs[name]) {
        tabs[name].setAttribute("aria-selected", String(mode === name));
        tabs[name].tabIndex = mode === name ? 0 : -1;
      }
      if (panels[name]) panels[name].hidden = mode !== name;
    }
  }
  function clearSuggestions() {
    if (suggestions) suggestions.replaceChildren();
    searchMatches = [];
    searchActive = -1;
    if (field) {
      field.setAttribute("aria-expanded", "false");
      field.removeAttribute("aria-activedescendant");
    }
  }
  function focusOn(i, writeHash = true) {
    if (!validIndex(i)) return;
    focus = i;
    if (field) field.value = nodes[i].name;
    clearSuggestions();
    listLimit = pageSize;
    setMode("references");
    if (writeHash) setHash(declarationHash(nodes[i]), "references");
    renderReferences();
  }
  function selectProof(id, writeHash = true) {
    if (!activePreset || !activePreset.node_ids.includes(id) || !proofById.has(id)) return;
    selectedProof = id;
    setMode("overview");
    const node = proofById.get(id);
    if (validIndex(node.index)) {
      focus = node.index;
      if (field) field.value = nodes[focus].name;
      if (writeHash) setHash(declarationHash(nodes[focus]), "overview");
    }
    clearSuggestions();
    renderOverview();
  }
  function choosePreset(preset, writeHash = true) {
    if (!preset) return;
    activePreset = preset;
    selectedProof = preset.node_ids.includes(preset.root) ? preset.root : preset.node_ids[0];
    if (presetSelect) presetSelect.value = preset.id;
    setMode("overview");
    const node = proofById.get(selectedProof);
    if (node && validIndex(node.index)) {
      focus = node.index;
      if (field) field.value = nodes[focus].name;
    }
    clearSuggestions();
    if (writeHash) setHash("overview-" + preset.id, "overview");
    renderOverview();
  }
  function wrapText(text, maxLength, maxLines) {
    const words = String(text || "").trim().split(/\s+/).filter(Boolean);
    const lines = [];
    let line = "";
    for (const original of words) {
      // Long Lean identifiers are split visibly instead of overflowing a node.
      const chunks = original.length > maxLength ? original.match(new RegExp(".{1," + maxLength + "}", "g")) : [original];
      for (const word of chunks) {
        if (line && line.length + word.length + 1 > maxLength) { lines.push(line); line = word; }
        else line += (line ? " " : "") + word;
      }
    }
    if (line) lines.push(line);
    if (lines.length > maxLines) {
      lines.length = maxLines;
      lines[maxLines - 1] = lines[maxLines - 1].slice(0, maxLength - 1).replace(/[.,;:]$/, "") + "…";
    }
    return lines.length ? lines : [""];
  }
  function svgText(group, text, x, y, className, maxLength, maxLines, lineHeight) {
    const result = svgElement("text", {x, y, "text-anchor": "middle", class: className});
    const lines = wrapText(text, maxLength, maxLines);
    lines.forEach((line, i) => {
      const span = svgElement("tspan", {x, dy: i ? lineHeight : 0});
      span.textContent = line;
      result.appendChild(span);
    });
    group.appendChild(result);
    return lines.length;
  }
  function makeSVG(rows, titleText, markerId, overview = false, edges = []) {
    const width = overview ? 1060 : 820, rowHeight = 160;
    const height = Math.max(1, rows.length) * rowHeight + 20;
    const svg = svgElement("svg", {viewBox: `0 0 ${width} ${height}`, role: "group", "aria-label": titleText});
    const title = svgElement("title");
    title.textContent = titleText;
    svg.appendChild(title);
    const defs = svgElement("defs");
    const marker = svgElement("marker", {id: markerId, markerWidth: 9, markerHeight: 9, refX: 8, refY: 4.5, orient: "auto", markerUnits: "strokeWidth"});
    marker.appendChild(svgElement("path", {d: "M0,0 L9,4.5 L0,9 z", fill: "#72967e"}));
    defs.appendChild(marker);
    svg.appendChild(defs);
    const positions = new Map();
    // Leave side gutters for arrows that must pass intermediate rows.
    rows.forEach((row, n) => row.forEach((id, column) => positions.set(id, {x: 18 + (width - 36) * (column + 0.5) / row.length, y: n * rowHeight + 70, width: 184, height: 116})));
    if (overview) {
      // Work back from the conclusion so ingredients stay near their consumers.
      const consumers = new Map(rows.flat().map(id => [id, []]));
      edges.forEach(edge => consumers.get(edge.from).push(edge.to));
      for (let rowIndex = rows.length - 1; rowIndex >= 0; rowIndex--) {
        const desired = new Map(rows[rowIndex].map(id => {
          const targets = consumers.get(id).map(target => positions.get(target).x);
          return [id, targets.length ? targets.reduce((sum, x) => sum + x, 0) / targets.length : width / 2];
        }));
        const ordered = rows[rowIndex].slice().sort((a, b) => desired.get(a) - desired.get(b));
        const gap = 202;
        // Isotonic projection gives the closest ordered, nonoverlapping positions.
        const blocks = [];
        ordered.forEach((id, i) => {
          blocks.push({start: i, end: i, sum: desired.get(id) - i * gap, count: 1});
          while (blocks.length > 1) {
            const right = blocks[blocks.length - 1], left = blocks[blocks.length - 2];
            if (left.sum / left.count <= right.sum / right.count) break;
            blocks.splice(-2, 2, {start: left.start, end: right.end, sum: left.sum + right.sum, count: left.count + right.count});
          }
        });
        const minimum = 120, maximum = width - 120 - (ordered.length - 1) * gap;
        for (const block of blocks) {
          const offset = Math.max(minimum, Math.min(maximum, block.sum / block.count));
          for (let i = block.start; i <= block.end; i++) positions.get(ordered[i]).x = offset + i * gap;
        }
      }
    }
    svg.diagramWidth = width;
    svg.routeLanes = {left: 0, right: 0};
    return {svg, positions};
  }
  function drawEdge(svg, positions, from, to, markerId, className) {
    const a = positions.get(from), b = positions.get(to);
    if (!a || !b || from === to) return;
    let path, points;
    if (a.y === b.y) {
      const sign = b.x >= a.x ? 1 : -1;
      const start = a.x + sign * a.width / 2, end = b.x - sign * (b.width / 2 + 5);
      path = `M${start},${a.y} C${start + sign * 24},${a.y - 32} ${end - sign * 24},${b.y - 32} ${end},${b.y}`;
      points = [start, a.y, start + sign * 24, a.y - 32, end - sign * 24, b.y - 32, end, b.y];
    } else {
      const sign = b.y >= a.y ? 1 : -1;
      const start = a.y + sign * a.height / 2, end = b.y - sign * (b.height / 2 + 5);
      const middle = (start + end) / 2;
      path = `M${a.x},${start} C${a.x},${middle} ${b.x},${middle} ${b.x},${end}`;
      points = [a.x, start, a.x, middle, b.x, middle, b.x, end];
    }
    const obstacles = [...positions.entries()].filter(([id]) => id !== from && id !== to).map(([, position]) => position);
    const blocked = obstacles.some(obstacle => {
      for (let step = 1; step < 80; step++) {
        const t = step / 80, u = 1 - t;
        const x = u * u * u * points[0] + 3 * u * u * t * points[2] + 3 * u * t * t * points[4] + t * t * t * points[6];
        const y = u * u * u * points[1] + 3 * u * u * t * points[3] + 3 * u * t * t * points[5] + t * t * t * points[7];
        if (Math.abs(x - obstacle.x) < obstacle.width / 2 + 5 && Math.abs(y - obstacle.y) < obstacle.height / 2 + 5) return true;
      }
      return false;
    });
    if (blocked && a.y === b.y) {
      const laneY = a.y - a.height / 2 - 16;
      path = `M${a.x},${a.y - a.height / 2} L${a.x},${laneY} L${b.x},${laneY} L${b.x},${b.y - b.height / 2 - 5}`;
    } else if (blocked) {
      const sign = b.y >= a.y ? 1 : -1;
      const diagramWidth = svg.diagramWidth || 820;
      const side = a.x + b.x < diagramWidth ? "left" : "right";
      const laneNumber = svg.routeLanes[side]++ % 7;
      const laneX = side === "left" ? 4 + laneNumber * 2.4 : diagramWidth - 4 - laneNumber * 2.4;
      const start = a.y + sign * a.height / 2, end = b.y - sign * (b.height / 2 + 5);
      const exit = start + sign * 16, approach = end - sign * 11;
      path = `M${a.x},${start} L${a.x},${exit} L${laneX},${exit} L${laneX},${approach} L${b.x},${approach} L${b.x},${end}`;
    }
    svg.appendChild(svgElement("path", {d: path, class: className || "proof-edge", "data-from": from, "data-to": to, fill: "none", stroke: "#72967e", "stroke-width": 1.8, "marker-end": `url(#${markerId})`}));
  }
  function drawNode(svg, position, node, id, selected, connected, onSelect, advanced = false) {
    const classes = ["proof-node", selected ? "proof-node-selected" : connected ? "proof-node-connected" : "proof-node-dim"];
    if (advanced) classes.push("graph-node");
    const group = svgElement("g", {class: classes.join(" "), tabindex: 0, role: "button", "aria-label": "Select " + labelFor(node), "aria-pressed": String(selected), "data-node": id});
    const title = svgElement("title");
    title.textContent = labelFor(node) + (node.description ? "\n" + node.description : "") + (node.name ? "\n" + node.name : "");
    group.appendChild(title);
    group.appendChild(svgElement("rect", {x: position.x - position.width / 2, y: position.y - position.height / 2, width: position.width, height: position.height, rx: 8}));
    const lines = svgText(group, labelFor(node), position.x, position.y - 32, "proof-node-title", 23, 3, 17);
    const formula = node.map_note || node.formula || (advanced ? node.kind + (node.internal ? " · Lean helper" : "") : "");
    svgText(group, formula, position.x, position.y - 32 + lines * 17 + 8, "proof-node-formula", 26, 2, 15);
    group.addEventListener("click", onSelect);
    group.addEventListener("keydown", event => {
      if (event.key !== "Enter" && event.key !== " ") return;
      event.preventDefault();
      const host = svg.parentElement;
      onSelect();
      // Rerendering replaces the SVG: keep keyboard focus on the selected node.
      focusDiagramNode(host, id);
    });
    svg.appendChild(group);
  }
  function focusDiagramNode(host, id) {
    if (!host) return;
    const replacement = [...host.querySelectorAll("g[data-node]")].find(item => item.getAttribute("data-node") === String(id));
    if (replacement) replacement.focus();
  }
  function proofEdges() {
    const visible = new Set(activePreset.node_ids);
    return (activePreset.edges || []).filter(edge => visible.has(edge.from) && visible.has(edge.to) && proofById.has(edge.from) && proofById.has(edge.to));
  }
  function proofRows(edges) {
    const ids = activePreset.node_ids.filter(id => proofById.has(id));
    const degree = new Map(ids.map(id => [id, 0])), outgoing = new Map(ids.map(id => [id, []]));
    edges.forEach(edge => { degree.set(edge.to, degree.get(edge.to) + 1); outgoing.get(edge.from).push(edge.to); });
    const queue = ids.filter(id => degree.get(id) === 0), visited = [];
    while (queue.length) {
      const id = queue.shift();
      visited.push(id);
      for (const next of outgoing.get(id)) {
        degree.set(next, degree.get(next) - 1);
        if (degree.get(next) === 0) queue.push(next);
      }
    }
    const distance = new Map(ids.map(id => [id, 0]));
    for (const id of visited.reverse()) {
      for (const next of outgoing.get(id)) distance.set(id, Math.max(distance.get(id), distance.get(next) + 1));
    }
    // Delay each input until the layer where it supports its next conclusion.
    const maximum = Math.max(0, ...distance.values());
    const levels = new Map(ids.map(id => [id, maximum - distance.get(id)]));
    const rows = [];
    for (let level = 0; level <= maximum; level++) {
      const group = ids.filter(id => levels.get(id) === level);
      for (let i = 0; i < group.length; i += 5) rows.push(group.slice(i, i + 5));
    }
    return rows;
  }
  function statementLinks(host, declaration, includePreview = true) {
    if (!declaration) return;
    const links = element("p", "proof-statement-links");
    links.appendChild(link(declaration.url, "Exact Lean statement"));
    const source = declaration.source_url || declaration.module_url;
    if (source) { links.appendChild(document.createTextNode(" · ")); links.appendChild(link(source, "Exact Lean source")); }
    host.appendChild(links);
    if (includePreview && declaration.statement) {
      const details = element("details", "proof-statement-preview");
      details.appendChild(element("summary", "", "Lean statement preview"));
      const pre = element("pre");
      pre.appendChild(element("code", "", declaration.statement));
      details.appendChild(pre);
      if (declaration.statement_truncated) details.appendChild(element("p", "small muted", "This preview is shortened. Open the exact Lean statement for the complete declaration."));
      host.appendChild(details);
    }
  }
  function edgePath(edge) {
    const details = element("details", "proof-edge-path");
    const path = (edge.path || []).filter(validIndex);
    details.appendChild(element("summary", "", "Inspect the exact reference path (" + Math.max(0, path.length - 1) + " direct steps)"));
    details.appendChild(element("p", "small muted", "The exported path runs from the consuming declaration back to its prerequisite. Each consecutive declaration directly references the next in its proof or definition."));
    const ordered = element("ol", "proof-path-list");
    for (const i of path) {
      const item = element("li");
      item.appendChild(link(nodes[i].url, nodes[i].name, "neighbor-identifier"));
      if (nodes[i].label) item.appendChild(element("span", "proof-path-label", " — " + nodes[i].label));
      ordered.appendChild(item);
    }
    if (!path.length) details.appendChild(element("p", "small muted", "No exported reference path is available for this step."));
    else details.appendChild(ordered);
    return details;
  }
  function stepList(host, titleText, edges, incoming) {
    host.appendChild(element("h3", "", titleText));
    if (!edges.length) {
      host.appendChild(element("p", "small muted", incoming ? "This is an input to this overview; no earlier step is included in this route." : "This is a conclusion of this overview; no later step is included in this route."));
      return;
    }
    const ordered = element("ul", "proof-step-list");
    for (const edge of edges) {
      const nextId = incoming ? edge.from : edge.to, next = proofById.get(nextId);
      const item = element("li");
      item.appendChild(button(labelFor(next), event => {
        selectProof(nextId);
        if (event.detail === 0) focusDiagramNode(proofMap, nextId);
      }, "proof-step-button"));
      if (next.formula) item.appendChild(element("p", "proof-formula", next.formula));
      if (next.description) item.appendChild(element("p", "proof-step-description", next.description));
      item.appendChild(edgePath(edge));
      ordered.appendChild(item);
    }
    host.appendChild(ordered);
  }
  function renderOverview() {
    if (!activePreset || !proofMap || !proofDetail) return;
    const selected = proofById.get(selectedProof) || proofById.get(activePreset.root);
    if (!selected) return;
    selectedProof = selected.id;
    const edges = proofEdges(), incoming = edges.filter(edge => edge.to === selectedProof), outgoing = edges.filter(edge => edge.from === selectedProof);
    const connected = new Set([...incoming.map(edge => edge.from), ...outgoing.map(edge => edge.to)]);
    const {svg, positions} = makeSVG(proofRows(edges), "Mathematical proof overview. Arrows run from an ingredient to the conclusion it supports.", "proof-arrow", true, edges);
    edges.forEach(edge => drawEdge(svg, positions, edge.from, edge.to, "proof-arrow", edge.from === selectedProof || edge.to === selectedProof ? "proof-edge proof-edge-connected" : "proof-edge proof-edge-dim"));
    for (const [id, position] of positions) drawNode(svg, position, proofById.get(id), id, id === selectedProof, connected.has(id), () => selectProof(id));
    proofMap.replaceChildren(svg);
    proofDetail.replaceChildren();
    proofDetail.appendChild(element("h2", "proof-detail-title", selected.label));
    if (selected.formula) proofDetail.appendChild(element("p", "proof-formula", selected.formula));
    if (selected.description) proofDetail.appendChild(element("p", "proof-detail-description", selected.description));
    const declaration = validIndex(selected.index) ? nodes[selected.index] : undefined;
    statementLinks(proofDetail, declaration);
    if (declaration) proofDetail.appendChild(button("Explore all references for this declaration", event => {
      focusOn(selected.index);
      if (event.detail === 0 && field) field.focus();
    }, "button proof-open-references"));
    stepList(proofDetail, "Ingredients used here", incoming, true);
    stepList(proofDetail, "What this helps prove", outgoing, false);
    if (proofStatus) proofStatus.textContent = (activePreset.description ? activePreset.description + " " : "") + positions.size + " mathematical steps. Select a step to see its meaning and the exact Lean references behind each arrow.";
  }
  function referenceLevels() {
    const maximum = Math.max(1, Number(depth.value) || 1), levels = [[focus]], reached = new Set([focus]);
    for (let level = 0; level < maximum; level++) {
      const next = [...new Set(levels[level].flatMap(refs))].filter(i => !reached.has(i)).sort(compare);
      if (!next.length) break;
      next.forEach(i => reached.add(i));
      levels.push(next);
    }
    let remaining = graphLimit;
    const displayed = levels.map(level => {
      const selected = level.slice(0, remaining);
      remaining -= selected.length;
      return selected;
    }).filter(level => level.length);
    if (direction.value === "dependencies") displayed.reverse();
    const rows = [];
    for (const level of displayed) for (let i = 0; i < level.length; i += 4) rows.push(level.slice(i, i + 4));
    return {rows, reached, maximum};
  }
  function drawReferences() {
    if (!graph || !validIndex(focus)) return;
    const {rows, reached, maximum} = referenceLevels();
    const {svg, positions} = makeSVG(rows, "Exact project references. Arrows always point from a referenced prerequisite to the declaration that consumes it.", "reference-arrow");
    const seenEdges = new Set();
    for (const i of positions.keys()) {
      for (const j of refs(i)) {
        if (!positions.has(j) || i === j) continue;
        const from = direction.value === "users" ? i : j, to = direction.value === "users" ? j : i;
        const key = from + ":" + to;
        if (seenEdges.has(key)) continue;
        seenEdges.add(key);
        drawEdge(svg, positions, from, to, "reference-arrow", "proof-edge");
      }
    }
    const direct = new Set(refs(focus));
    for (const [i, position] of positions) drawNode(svg, position, nodes[i], i, i === focus, direct.has(i), () => focusOn(i), true);
    graph.replaceChildren(svg);
    const omitted = reached.size - positions.size;
    status.textContent = positions.size + " of " + reached.size.toLocaleString() + " declarations within depth " + maximum + "; " + seenEdges.size + " visible direct reference edges. " + (omitted ? omitted.toLocaleString() + " declarations are omitted from the diagram's " + graphLimit + "-node limit. " : "Every matching declaration within this depth is shown. ") + "The complete matching direct-reference list is below. Arrows always run from prerequisite to consumer.";
  }
  function renderReferences() {
    if (!validIndex(focus) || !focusText || !list) return;
    const node = nodes[focus];
    focusText.replaceChildren();
    focusText.appendChild(element("h2", "proof-detail-title", labelFor(node)));
    if (node.description) focusText.appendChild(element("p", "", node.description));
    focusText.appendChild(link(node.url, node.name, "neighbor-identifier"));
    if (node.internal) focusText.appendChild(element("p", "small muted", "This selected declaration is a Lean helper. It stays selected while the helper filter controls its neighbors."));
    statementLinks(focusText, node);
    drawReferences();
    const neighbors = refs(focus), hidden = allRefs(focus).length - neighbors.length;
    list.replaceChildren();
    const relation = direction.value === "users" ? "direct consumers" : "direct prerequisites";
    list.appendChild(element("p", "small muted", neighbors.length.toLocaleString() + " matching " + relation + "; showing " + Math.min(listLimit, neighbors.length).toLocaleString() + "." + (hidden ? " " + hidden.toLocaleString() + " Lean helpers are hidden; enable the helper filter to include them." : "")));
    for (const i of neighbors.slice(0, listLimit)) {
      const row = element("div", "neighbor-row"), copy = element("div", "neighbor-copy");
      const select = button(labelFor(nodes[i]), event => {
        focusOn(i);
        if (event.detail === 0) focusDiagramNode(graph, i);
      }, "neighbor-title neighbor-focus");
      select.setAttribute("aria-label", "Explore " + labelFor(nodes[i]) + ": " + nodes[i].name);
      copy.appendChild(select);
      if (nodes[i].description) copy.appendChild(element("p", "neighbor-description", nodes[i].description));
      copy.appendChild(link(nodes[i].url, nodes[i].name, "neighbor-identifier"));
      if (nodes[i].internal) copy.appendChild(element("span", "neighbor-helper small muted", " · Lean helper"));
      row.appendChild(copy);
      list.appendChild(row);
    }
    if (!neighbors.length) list.appendChild(element("p", "small muted", hidden ? "No references match the current helper filter." : "No direct project references match these controls."));
    if (more) {
      more.hidden = listLimit >= neighbors.length;
      more.textContent = "Show " + Math.min(pageSize, Math.max(0, neighbors.length - listLimit)) + " more references";
    }
  }
  function renderSuggestions() {
    clearSuggestions();
    const words = field.value.toLowerCase().trim().split(/\s+/).filter(Boolean);
    if (!words.length) return;
    const query = field.value.toLowerCase().trim();
    searchMatches = nodes.map((node, i) => i).filter(i => {
      const node = nodes[i], searchable = [node.name, node.module, node.label, node.description].filter(Boolean).join(" ").toLowerCase();
      return words.every(word => searchable.includes(word));
    }).sort((a, b) => Number(nodes[b].name.toLowerCase() === query) - Number(nodes[a].name.toLowerCase() === query) || compare(a, b)).slice(0, 8);
    for (const [position, i] of searchMatches.entries()) {
      const suggestion = button("", () => focusOn(i), "dependency-suggestion");
      suggestion.id = "dependency-suggestion-" + position;
      suggestion.setAttribute("role", "option");
      suggestion.setAttribute("aria-selected", "false");
      suggestion.appendChild(element("span", "neighbor-title", labelFor(nodes[i])));
      suggestion.appendChild(element("span", "neighbor-identifier", nodes[i].name + (nodes[i].internal ? " · Lean helper" : "")));
      suggestions.appendChild(suggestion);
    }
    if (!searchMatches.length) suggestions.appendChild(element("p", "small muted", "No matching project declaration."));
    field.setAttribute("aria-expanded", String(searchMatches.length > 0));
  }
  function moveSuggestion(next) {
    if (!searchMatches.length) return;
    searchActive = (next + searchMatches.length) % searchMatches.length;
    suggestions.querySelectorAll("button").forEach((item, i) => item.setAttribute("aria-selected", String(i === searchActive)));
    field.setAttribute("aria-activedescendant", "dependency-suggestion-" + searchActive);
  }
  function routeFromHash() {
    const hash = location.hash.slice(1), preset = presets.find(item => hash === "overview-" + item.id);
    if (!hash) {
      if (presets.length) choosePreset(presets[0], false);
      else focusOn(byName.get(explorer.dataset.focus) ?? 0, false);
      return;
    }
    if (preset) { choosePreset(preset, false); return; }
    const i = byHash.get(hash);
    if (i !== undefined) {
      const mapped = proofByIndex.get(i), storedMode = history.state && history.state.dependencyMode;
      if (mapped && storedMode !== "references") {
        const preferred = history.state && presets.find(item => item.id === history.state.dependencyPreset && item.node_ids.includes(mapped.id));
        const containing = preferred || (activePreset && activePreset.node_ids.includes(mapped.id) ? activePreset : presets.find(item => item.node_ids.includes(mapped.id)));
        if (containing) { activePreset = containing; if (presetSelect) presetSelect.value = containing.id; selectProof(mapped.id, false); return; }
      }
      focusOn(i, false);
      return;
    }
    if (mode === "overview") renderOverview();
    else renderReferences();
  }
  if (presetSelect) {
    presetSelect.replaceChildren();
    for (const preset of presets) { const option = element("option", "", preset.label); option.value = preset.id; presetSelect.appendChild(option); }
    presetSelect.addEventListener("change", () => choosePreset(presets.find(preset => preset.id === presetSelect.value)));
  }
  for (const name of ["overview", "references"]) {
    if (!tabs[name]) continue;
    tabs[name].addEventListener("click", () => {
      if (name === "overview") {
        const mapped = proofByIndex.get(focus);
        const containing = mapped && (activePreset && activePreset.node_ids.includes(mapped.id) ? activePreset : presets.find(preset => preset.node_ids.includes(mapped.id)));
        if (containing) {
          activePreset = containing;
          if (presetSelect) presetSelect.value = containing.id;
          selectProof(mapped.id);
        } else if (selectedProof) selectProof(selectedProof);
        else choosePreset(activePreset);
      } else focusOn(focus);
    });
    tabs[name].addEventListener("keydown", event => {
      if (!["ArrowLeft", "ArrowRight", "Home", "End"].includes(event.key)) return;
      event.preventDefault();
      const target = event.key === "Home" ? "overview" : event.key === "End" ? "references" : name === "overview" ? "references" : "overview";
      if (tabs[target]) { tabs[target].click(); tabs[target].focus(); }
    });
  }
  if (field && suggestions) {
    field.setAttribute("role", "combobox");
    field.setAttribute("aria-autocomplete", "list");
    field.setAttribute("aria-controls", "dependency-suggestions");
    field.setAttribute("aria-expanded", "false");
    suggestions.setAttribute("role", "listbox");
    suggestions.setAttribute("aria-label", "Matching Lean declarations");
    field.addEventListener("input", renderSuggestions);
    field.addEventListener("keydown", event => {
      if (event.key === "ArrowDown" || event.key === "ArrowUp") {
        event.preventDefault();
        if (!searchMatches.length) renderSuggestions();
        moveSuggestion(searchActive < 0 ? (event.key === "ArrowDown" ? 0 : searchMatches.length - 1) : searchActive + (event.key === "ArrowDown" ? 1 : -1));
      } else if (event.key === "Enter") {
        event.preventDefault();
        const exact = byName.get(field.value.trim()), selected = searchMatches[searchActive];
        if (selected !== undefined) focusOn(selected);
        else if (exact !== undefined) focusOn(exact);
        else if (searchMatches.length) focusOn(searchMatches[0]);
        else { renderSuggestions(); if (searchMatches.length) focusOn(searchMatches[0]); }
      } else if (event.key === "Escape") clearSuggestions();
    });
    explorer.addEventListener("click", event => { if (event.target !== field && !suggestions.contains(event.target)) clearSuggestions(); });
  }
  for (const control of [direction, kind, depth, helpers]) if (control) control.addEventListener("change", () => { listLimit = pageSize; renderReferences(); });
  if (more) more.addEventListener("click", () => { listLimit += pageSize; renderReferences(); });
  const collapse = get("dependency-collapse");
  if (collapse) collapse.addEventListener("click", () => { depth.value = "1"; renderReferences(); });
  window.addEventListener("hashchange", routeFromHash);
  window.addEventListener("popstate", routeFromHash);
  if (!nodes.length) {
    setMode("references");
    if (status) status.textContent = "No declaration reference data is available.";
    return;
  }
  if (field) field.value = nodes[focus].name;
  setMode(mode);
  renderReferences();
  routeFromHash();
})();
