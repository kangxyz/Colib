"use strict";

const elements = {
  entries: document.querySelector("#entries"),
  topics: document.querySelector("#topics"),
  search: document.querySelector("#search"),
  count: document.querySelector("#result-count"),
  heading: document.querySelector("#subject-heading"),
  empty: document.querySelector("#empty"),
};

let catalog;
let selectedTopic = "";

function node(tag, className, text) {
  const element = document.createElement(tag);
  if (className) element.className = className;
  if (text !== undefined) element.textContent = text;
  return element;
}

function link(text, url, className) {
  const element = node("a", className, text);
  element.href = url;
  return element;
}

function renderEntry(entry) {
  const article = node("article", "entry");
  article.id = entry.id;
  const top = node("div", "entry-top");
  top.append(link(entry.id, "#" + entry.id, "id"), node("span", "relation", entry.relation));
  article.append(top, node("h3", "", entry.title), node("p", "statement", entry.statement));
  article.append(link(entry.locator + " ↗", entry.url, "reference"));
  const scope = node("p", "scope");
  scope.append(node("strong", "", "Correspondence scope"), document.createTextNode(entry.scope));
  article.append(scope);

  const details = node("details");
  details.append(node("summary", "", "Lean declarations · " + entry.declarations.length));
  for (const name of entry.declarations) {
    const declaration = catalog.declarations[name];
    const block = node("div", "declaration");
    block.append(link(name + " ↗", declaration.source_url, "declaration-title"));
    const importRow = node("pre", "import");
    const importText = "import " + declaration.module;
    importRow.append(node("code", "", importText));
    const copy = node("button", "copy", "Copy");
    copy.type = "button";
    copy.setAttribute("aria-label", "Copy import for " + name);
    copy.addEventListener("click", async () => {
      try {
        await navigator.clipboard.writeText(importText);
        copy.textContent = "Copied";
        setTimeout(() => { copy.textContent = "Copy"; }, 1400);
      } catch {
        copy.textContent = "Select import";
      }
    });
    importRow.append(copy);
    const signature = node("pre");
    signature.append(node("code", "", declaration.type));
    block.append(importRow, signature);
    details.append(block);
  }
  article.append(details, node("p", "review", "Source correspondence · author-checked"));
  return article;
}

function render() {
  const query = elements.search.value.trim().toLocaleLowerCase();
  const matches = catalog.entries.filter((entry) => {
    const text = [entry.id, entry.title, entry.statement, entry.locator,
      entry.scope, ...entry.declarations].join(" ").toLocaleLowerCase();
    return (!selectedTopic || selectedTopic === entry.topic) && (!query || text.includes(query));
  });
  elements.entries.replaceChildren(...matches.map(renderEntry));
  elements.count.textContent = matches.length + " of " + catalog.entries.length + " entries";
  elements.heading.textContent = selectedTopic || "All results";
  elements.empty.hidden = matches.length !== 0;
  for (const button of elements.topics.querySelectorAll("button")) {
    const active = button.dataset.topic === selectedTopic;
    button.classList.toggle("active", active);
    button.setAttribute("aria-pressed", String(active));
  }
}

function navigateToHash() {
  if (!location.hash.startsWith("#COL-")) return;
  selectedTopic = "";
  elements.search.value = "";
  render();
  document.getElementById(location.hash.slice(1))?.scrollIntoView();
}

async function start() {
  const response = await fetch("catalog.json");
  if (!response.ok) throw new Error("The catalog could not be loaded.");
  catalog = await response.json();
  const subjects = [...new Set(catalog.entries.map((entry) => entry.topic))];
  for (const topic of ["", ...subjects]) {
    const button = node("button", "topic", topic || "All results");
    button.type = "button";
    button.dataset.topic = topic;
    button.append(node("span", "", topic
      ? catalog.entries.filter((entry) => entry.topic === topic).length
      : catalog.entries.length));
    button.addEventListener("click", () => {
      selectedTopic = topic;
      render();
    });
    elements.topics.append(button);
  }
  const facts = document.querySelector("#facts");
  facts.replaceChildren();
  for (const [amount, description] of [
    [catalog.entries.length, "mathematical entries"],
    [Object.keys(catalog.declarations).length, "Lean declarations"],
    [subjects.length, "subjects"],
  ]) {
    const item = node("span");
    item.append(node("strong", "", amount), document.createTextNode(description));
    facts.append(item);
  }
  const revision = document.querySelector("#revision");
  revision.textContent = "Lean source · " + catalog.revision.slice(0, 7) + " ↗";
  revision.href = "https://github.com/kangxyz/colib/tree/" + catalog.revision;
  const bibliography = document.querySelector("#source-list");
  for (const source of Object.values(catalog.sources)) {
    const article = node("article", "source");
    const heading = node("h3");
    heading.append(link(source.title, source.url));
    article.append(heading, node("p", "", source.authors.join(", ")),
      node("p", "", source.version));
    bibliography.append(article);
  }
  elements.search.addEventListener("input", render);
  window.addEventListener("hashchange", navigateToHash);
  document.addEventListener("keydown", (event) => {
    if (event.key === "/" && !["INPUT", "TEXTAREA"].includes(document.activeElement.tagName)) {
      event.preventDefault();
      elements.search.focus();
    }
  });
  render();
  navigateToHash();
}

start().catch((error) => {
  elements.entries.append(node("p", "empty", error.message));
  document.querySelector("#facts").textContent = "Catalog unavailable";
});
