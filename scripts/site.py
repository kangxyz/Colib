#!/usr/bin/env python3
"""Generate chapter, section, item and bibliography pages for the Colib Library."""

import argparse
from html import escape
import json
from pathlib import Path
import shutil

import catalog


def anchor(text, path):
    return f'<a href="{escape(path, quote=True)}">{escape(text)}</a>'


def build(library_path, output):
    library = json.loads(Path(library_path).read_text())
    if (
        library.get("schema") != 2
        or library.get("source_hashes") != catalog.source_hashes()
    ):
        raise ValueError(
            "Build the Library export for the current Lean source and pins first"
        )
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    chapters = library["chapters"]
    sections = library["sections"]
    entries = library["entries"]
    template = (catalog.ROOT / "docs/site/index.html").read_text()
    reading_order = [
        identifier
        for chapter in chapters
        for section_id in chapter["sections"]
        for identifier in sections[section_id]["entries"]
    ]
    positions = {identifier: index for index, identifier in enumerate(reading_order)}
    chapter_lookup = {chapter["id"]: chapter for chapter in chapters}
    numbers, module_items, source_items, citations_by_module = {}, {}, {}, {}
    declarations_by_module, citations_by_declaration = {}, {}
    for declaration in library["declarations"].values():
        declarations_by_module.setdefault(declaration["module"], []).append(declaration)
    for chapter_index, chapter in enumerate(chapters, 1):
        for section_index, section_id in enumerate(chapter["sections"], 1):
            for item_index, identifier in enumerate(sections[section_id]["entries"], 1):
                numbers[identifier] = f"{chapter_index}.{section_index}.{item_index}"
    for identifier, entry in entries.items():
        for name in entry["declarations"]:
            module = library["declarations"][name]["module"]
            module_items.setdefault(module, set()).add(identifier)
        for citation in entry["references"]:
            source_items.setdefault(citation["source"], set()).add(identifier)
    for citation in library.get("citations", []):
        module = library["declarations"][citation["name"]]["module"]
        citations_by_module.setdefault(module, []).append(citation)
        citations_by_declaration.setdefault(citation["name"], []).append(citation)

    def render_page(path, title, content, active_section="", breadcrumbs=()):
        depth = len(Path(path).parts) - 1
        root = "../" * depth if depth else "./"
        navigation = []
        for chapter in chapters:
            navigation.append(
                '<div class="nav-chapter">'
                + anchor(chapter["title"], root + "chapters/" + chapter["id"] + "/")
            )
            for section_id in chapter["sections"]:
                section = sections[section_id]
                active = (
                    ' class="active" aria-current="page"'
                    if section_id == active_section
                    else ""
                )
                navigation.append(
                    f'<a{active} href="{root}sections/{section_id}/">'
                    + escape(section["title"])
                    + f'<span>{len(section["entries"])}</span></a>'
                )
            navigation.append("</div>")
        trail = [anchor("Library", root)]
        trail.extend(anchor(label, root + href) for label, href in breadcrumbs)
        values = {
            "title": escape(title + " — Colib Library"),
            "root": root,
            "home": "true" if path == "index.html" else "false",
            "navigation": "".join(navigation),
            "content": content,
            "breadcrumbs": '<nav class="breadcrumbs" aria-label="Breadcrumb">'
            + '<span aria-hidden="true">/</span>'.join(trail)
            + "</nav>",
            "revision": library["revision"],
            "short_revision": library["revision"][:7],
        }
        text = template
        for key, value in values.items():
            text = text.replace("{{" + key + "}}", value)
        target = output / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def item_link(identifier):
        entry = entries[identifier]
        return anchor(
            identifier + " · " + entry["title"], "../../tag/" + identifier + "/"
        )

    def render_item(identifier, root, heading="h2"):
        entry = entries[identifier]
        section = sections[entry["section"]]
        number = numbers[identifier]
        pieces = [
            f'<article class="item" id="{identifier}">',
            '<div class="item-label">'
            + escape(entry["kind"].title() + " " + number)
            + " · "
            + anchor(identifier, root + "tag/" + identifier + "/")
            + "</div>",
            "<" + heading + ">" + escape(entry["title"]) + "</" + heading + ">",
            '<p class="statement">' + escape(entry["statement"]) + "</p>",
            '<p class="scope">' + escape(entry["scope"]) + "</p>",
        ]
        for field, label in (
            ("used_by", "Referenced by"),
            ("formal_dependencies", "Direct Lean references"),
        ):
            ids = entry.get(field, [])
            if ids:
                pieces.append(
                    '<p class="relations"><strong>'
                    + label
                    + "</strong> "
                    + " · ".join(
                        anchor(value, root + "tag/" + value + "/") for value in ids
                    )
                    + "</p>"
                )
        if entry.get("proof"):
            pieces.extend(
                [
                    '<details class="proof"><summary>Proof outline</summary><p>',
                    escape(entry["proof"]),
                    "</p></details>",
                ]
            )
        pieces.append('<div class="citations"><h3>References</h3><ul>')
        seen = set()
        for citation in entry["references"]:
            identity = (
                citation["source"],
                citation["locator"],
                citation["relation"],
                citation["scope"],
            )
            if identity in seen:
                continue
            seen.add(identity)
            source = library["sources"][citation["source"]]
            pieces.append(
                "<li>"
                + anchor(source["title"], citation["url"])
                + ", "
                + escape(citation["locator"])
                + ". <span>"
                + escape(
                    "Scope"
                    if citation["relation"] == "source_tag"
                    else citation["relation"].title()
                )
                + (". " + escape(citation["scope"]) if citation["scope"] else "")
                + "</span></li>"
            )
        pieces.append(
            '</ul></div><details class="lean"><summary>Lean declarations · '
            + str(len(entry["declarations"]))
            + "</summary>"
        )
        for name in entry["declarations"]:
            declaration = library["declarations"][name]
            import_text = "import " + declaration["module"]
            pieces.append(
                '<div class="declaration">'
                + anchor(name + " ↗", declaration["source_url"])
                + '<pre class="import"><code>'
                + escape(import_text)
                + '</code><button class="copy" data-copy="'
                + escape(import_text, quote=True)
                + '">Copy</button></pre><pre><code>'
                + escape(declaration["type"])
                + "</code></pre></div>"
            )
        pieces.append(
            '</details><p class="review">Source correspondence · '
            + escape(entry["review"].replace("_", "-"))
            + "</p></article>"
        )
        return "".join(pieces)

    home = [
        '<p class="eyebrow">COHOMOLOGY · HOMOTOPY · ALGEBRAIC GEOMETRY</p>',
        "<h1>Colib Library</h1>",
        '<p class="lede">The mathematical organization of Colib, from definitions and prerequisites '
        "to theorems, comparisons and their precise literature references.</p>",
        f'<p class="edition">{len(chapters)} chapters · {len(sections)} sections · {len(entries)} permanent items</p>',
        "<h2>Contents</h2>",
    ]
    for index, chapter in enumerate(chapters, 1):
        home.append(
            '<section class="chapter-overview"><h3>'
            + anchor(f'{index}. {chapter["title"]}', "chapters/" + chapter["id"] + "/")
            + "</h3><p>"
            + escape(chapter["introduction"])
            + "</p><ol>"
        )
        for section_id in chapter["sections"]:
            section = sections[section_id]
            home.append(
                "<li>"
                + anchor(section["title"], "sections/" + section_id + "/")
                + f' <span class="count">{len(section["entries"])} items</span></li>'
            )
        home.append("</ol></section>")
    home.append(
        '<p class="contribute">Contribute through the '
        + anchor(
            "Library organization and contribution guide",
            "https://github.com/kangxyz/colib/blob/main/CONTRIBUTING.md",
        )
        + ".</p>"
    )
    render_page("index.html", "Contents", "".join(home))
    for chapter in chapters:
        body = (
            "<h1>"
            + escape(chapter["title"])
            + '</h1><p class="lede">'
            + escape(chapter["introduction"])
            + "</p>"
        )
        for section_id in chapter["sections"]:
            section = sections[section_id]
            body += (
                '<section class="chapter-overview"><h2>'
                + anchor(section["title"], "../../sections/" + section_id + "/")
                + "</h2><p>"
                + escape(section["introduction"])
                + "</p><ol>"
            )
            body += (
                "".join(
                    "<li>" + item_link(identifier) + "</li>"
                    for identifier in section["entries"]
                )
                + "</ol></section>"
            )
        render_page("chapters/" + chapter["id"] + "/index.html", chapter["title"], body)
    for section_id, section in sections.items():
        chapter = chapter_lookup[section["chapter"]]
        trail = [(chapter["title"], "chapters/" + chapter["id"] + "/")]
        body = (
            "<h1>"
            + escape(section["title"])
            + '</h1><p class="lede">'
            + escape(section["introduction"])
            + "</p>"
        )
        body += (
            '<ol class="section-contents">'
            + "".join(
                "<li>"
                + anchor(
                    identifier + " · " + entries[identifier]["title"], "#" + identifier
                )
                + "</li>"
                for identifier in section["entries"]
            )
            + "</ol>"
        )
        body += "".join(
            render_item(identifier, "../../") for identifier in section["entries"]
        )
        render_page(
            "sections/" + section_id + "/index.html",
            section["title"],
            body,
            section_id,
            trail,
        )
        for index, identifier in enumerate(section["entries"]):
            body = render_item(identifier, "../../", heading="h1")
            neighbors = []
            position = positions[identifier]
            if position:
                neighbors.append("Previous · " + item_link(reading_order[position - 1]))
            if position + 1 < len(reading_order):
                neighbors.append("Next · " + item_link(reading_order[position + 1]))
            body += (
                '<nav class="reading-nav" aria-label="Reading order">'
                + "<br>".join(neighbors)
                + "</nav>"
            )
            render_page(
                "tag/" + identifier + "/index.html",
                identifier + " · " + entries[identifier]["title"],
                body,
                section_id,
                [*trail, (section["title"], "sections/" + section_id + "/")],
            )
    for identifier, item in library.get("retired", {}).items():
        previous_url = ("https://github.com/kangxyz/colib/blob/"
                        + item["previous_revision"] + "/" + item["previous_path"])
        body = ("<h1>" + escape(identifier + " · " + item["title"])
                + '</h1><p class="lede">Retired Library item</p><p>'
                + escape(item["reason"]) + "</p><p>"
                + anchor("Previous source record", previous_url) + "</p>")
        related = item.get("related_items", [])
        if related:
            body += "<p>Related maintained items: " + ", ".join(item_link(i) for i in related) + "</p>"
        render_page("tag/" + identifier + "/index.html", identifier + " · Retired", body)
    modules_index = [
        '<h1>Lean modules</h1><p class="lede">Code ownership and direct imports are read from the compiled Lean module system.</p>'
    ]
    for name, module in sorted(library["modules"].items()):
        matched = [
            entries[identifier]
            for identifier in sorted(module_items.get(name, set()), key=positions.get)
        ]
        body = (
            '<h1 class="module-title">'
            + escape(name)
            + "</h1><p>"
            + anchor("Lean source ↗", module["source_url"])
            + "</p>"
        )
        if matched:
            body += "<h2>Mathematical items</h2><ul>"
            body += (
                "".join("<li>" + item_link(entry["id"]) + "</li>" for entry in matched)
                + "</ul>"
            )
        owned = declarations_by_module.get(name, [])
        if owned:
            body += "<h2>Indexed declarations</h2>"
            for declaration in owned:
                body += (
                    '<details id="'
                    + escape(declaration["name"], quote=True)
                    + '"><summary>'
                )
                body += escape(declaration["name"]) + "</summary><p>"
                body += (
                    anchor("Lean source ↗", declaration["source_url"])
                    + "</p><pre><code>"
                )
                body += escape(declaration["type"]) + "</code></pre></details>"
        module_citations = citations_by_module.get(name, [])
        if module_citations:
            body += "<h2>Literature references of declarations</h2><ul>"
            for citation in module_citations:
                source = library["sources"][citation["source"]]
                body += (
                    "<li><code>"
                    + escape(citation["name"])
                    + "</code> · "
                    + anchor(
                        source["title"] + ", " + citation["locator"], citation["url"]
                    )
                    + "</li>"
                )
            body += "</ul>"
        body += "<h2>Direct imports</h2><ul>"
        for imported in module["imports"]:
            if imported in library["modules"]:
                body += "<li>" + anchor(imported, "../" + imported + "/") + "</li>"
            else:
                body += "<li><code>" + escape(imported) + "</code></li>"
        body += "</ul>"
        render_page(
            "modules/" + name + "/index.html",
            name,
            body,
            breadcrumbs=[("Lean modules", "modules/")],
        )
    module_tree = {}
    for name in sorted(library["modules"]):
        branch = module_tree
        for part in name.split("."):
            branch = branch.setdefault(part, {})
        branch[""] = name

    def render_module_tree(branch):
        parts = ['<ul class="module-tree">']
        for label, child in branch.items():
            if not label:
                continue
            name = child.get("")
            title = anchor(label, name + "/") if name else escape(label)
            children = any(key for key in child)
            if children:
                parts.append(
                    "<li><details open><summary>"
                    + title
                    + "</summary>"
                    + render_module_tree(child)
                    + "</details></li>"
                )
            else:
                count = len(module_items.get(name, set()))
                parts.append(
                    "<li>"
                    + title
                    + '<span class="count">'
                    + str(count)
                    + (" item" if count == 1 else " items")
                    + "</span></li>"
                )
        return "".join(parts) + "</ul>"

    modules_index.append(render_module_tree(module_tree))
    render_page("modules/index.html", "Lean modules", "".join(modules_index))
    sources_body = [
        '<h1>References</h1><p class="lede">Books, papers and reference works, with the inspected editions and exact item cross-references.</p>'
    ]
    source_order = {"reference_work": 1, "software": 2}
    ordered_sources = sorted(
        library["sources"].items(),
        key=lambda pair: (source_order.get(pair[1]["kind"], 0), pair[1]["title"]),
    )
    group = None
    for key, source in ordered_sources:
        source_group = source_order.get(source["kind"], 0)
        if source_group != group:
            group = source_group
            heading = {
                0: "Books and papers",
                1: "Reference works",
                2: "Implementation provenance",
            }[group]
            sources_body.append("<h2>" + heading + "</h2>")
        matched = [
            entries[identifier]
            for identifier in sorted(source_items.get(key, set()), key=positions.get)
        ]
        source_body = (
            "<h1>"
            + escape(source["title"])
            + "</h1><p>"
            + escape(", ".join(source["authors"]))
            + "</p><p>"
            + escape(source["version"])
            + "</p>"
        )
        source_body += "<p>" + anchor("Source record ↗", source["url"]) + "</p>"
        if source.get("doi"):
            source_body += "<p>DOI " + escape(source["doi"]) + "</p>"
        for document in source.get("documents", []):
            source_body += (
                "<details><summary>"
                + escape(document["label"])
                + "</summary><p>"
                + anchor("Inspected document ↗", document["url"])
                + '</p><code class="digest">SHA-256 '
                + escape(document["sha256"])
                + "</code></details>"
            )
        if matched:
            source_body += "<h2>Library correspondence</h2><ul>"
            for entry in matched:
                source_body += "<li>" + item_link(entry["id"]) + "<ul>"
                locators = sorted(
                    {
                        ref["locator"]
                        for ref in entry["references"]
                        if ref["source"] == key
                    }
                )
                source_body += (
                    "".join("<li>" + escape(locator) + "</li>" for locator in locators)
                    + "</ul></li>"
                )
            source_body += "</ul>"
        else:
            source_body += "<p>Implementation provenance is recorded in the owning item and source documentation.</p>"
        render_page(
            "references/" + key + "/index.html",
            source["title"],
            source_body,
            breadcrumbs=[("References", "references/")],
        )
        label = source["title"] + " · " + source["kind"].replace("_", " ")
        sources_body.append(
            '<section class="source"><h2>'
            + anchor(label, key + "/")
            + "</h2><p>"
            + escape(", ".join(source["authors"]))
            + "</p><p>"
            + escape(source["version"])
            + "</p>"
            + f"<p>{len(matched)} indexed mathematical items</p></section>"
        )
    render_page("references/index.html", "References", "".join(sources_body))
    render_page(
        "search/index.html",
        "Search",
        '<h1>Search the Library</h1><p id="search-status" role="status">Search by item, statement, Lean declaration or source locator.</p><div id="search-results"></div>',
    )
    search = []
    for entry in entries.values():
        terms = [
            entry["id"],
            entry["title"],
            entry["statement"],
            *entry["declarations"],
        ]
        for reference in entry["references"]:
            source = library["sources"][reference["source"]]
            terms.extend(
                [
                    reference["source"],
                    reference["locator"],
                    source["title"],
                    *source["authors"],
                ]
            )
        search.append(
            {
                "id": entry["id"],
                "title": entry["title"],
                "kind": entry["kind"],
                "section": sections[entry["section"]]["title"],
                "path": "tag/" + entry["id"] + "/",
                "statement": entry["statement"],
                "terms": " ".join(terms).casefold(),
            }
        )
    for identifier, item in library.get("retired", {}).items():
        search.append({
            "id": identifier, "title": item["title"], "kind": "retired",
            "section": "Retired items", "statement": item["reason"],
            "terms": " ".join([identifier, item["title"], item["reason"]]).casefold(),
        })
    for record in search:
        record["path"] = "tag/" + record["id"] + "/"
    for name, module in library["modules"].items():
        search.append(
            {
                "title": name,
                "kind": "module",
                "section": "Lean modules",
                "statement": "Defining module and its direct imports.",
                "terms": (" ".join([name, *module["imports"]])).casefold(),
                "path": "modules/" + name + "/",
            }
        )
    tagged_names = {
        name for entry in entries.values() for name in entry["declarations"]
    }
    for name, declaration in library["declarations"].items():
        if name in tagged_names:
            continue
        terms = [name, declaration["module"]]
        for citation in citations_by_declaration.get(name, []):
            source = library["sources"][citation["source"]]
            terms.extend(
                [
                    source["title"],
                    citation["source"],
                    citation["locator"],
                    *source["authors"],
                ]
            )
        search.append(
            {
                "title": name,
                "kind": "declaration",
                "section": declaration["module"],
                "statement": declaration["type"],
                "terms": " ".join(terms).casefold(),
                "path": "modules/" + declaration["module"] + "/#" + name,
            }
        )
    (output / "search.json").write_text(json.dumps(search, ensure_ascii=False) + "\n")
    for name in ("style.css", "site.js"):
        shutil.copyfile(catalog.ROOT / "docs/site" / name, output / name)
    (output / "library.json").write_text(
        json.dumps(library, ensure_ascii=False, indent=2) + "\n"
    )
    (output / "catalog.json").write_text(json.dumps(library, ensure_ascii=False) + "\n")
    (output / ".nojekyll").touch()
    print(
        f"Built the Library contents, {len(chapters)} chapters, {len(sections)} sections, "
        f'{len(entries)} item pages and {len(library["sources"])} reference pages'
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--library", type=Path, default=Path("build/library/library.json")
    )
    parser.add_argument("--output", type=Path, default=Path("build/site"))
    args = parser.parse_args()
    build(args.library, args.output)
