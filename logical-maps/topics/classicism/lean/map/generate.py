#!/usr/bin/env python3
"""Generate Classicism/Statements.lean with the map's own generator.

    python3 map/generate.py <logical-maps checkout> [--refs] [--patch]

Loads topics/classicism from the checkout, adds the fields of map/lean.yaml (as the map's
YAML would carry them once migrated), and runs pmap's generate_lean_statements, pointed at
this project, so that the statements Classicism/Map.lean proves are the map's, not a copy
of them. pmap is run with the change proposed in map/pmap.patch, applied in memory:

- a topic may say how a result concluding `False` is written (`lean.result.falsum`), so
  that an incompatibility reads "every schema entailing the premises is inconsistent";
- a principle may list equivalent forms (`forms`, each with a `lean_def`), and each form
  gets a statement: a schema entails the principle iff it entails the form.

With --refs, also fills `lean_ref` in map/lean.yaml from the certificates of results in
Classicism/Map.lean (a theorem named after a result id, in namespace Classicism.Map).
With --patch, writes map/pmap.patch, the proposed change as a diff against the checkout.
"""
from __future__ import annotations

import difflib
import re
import sys
import types
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
TOPIC = "classicism"

# The proposed change to scripts/pmap.py, as (old, new) replacements.
PMAP_CHANGES = [
    (
        'out += [pad + ("False" if item["conclusion"] == FALSE else fill(shape["principle"], item["conclusion"])), ""]',
        'out += [pad + (shape.get("falsum", "False") if item["conclusion"] == FALSE else fill(shape["principle"], item["conclusion"])), ""]',
    ),
    (
        '    out += [f"end {ns}.Statements", ""]',
        '''    # Equivalent forms of a principle: each is stated as equivalent to the official one.
    shape = cfg["result"]
    apply = lambda d: shape["principle"].replace("{def}", d)
    for p in data["principles"]:
        for form in p.get("forms") or []:
            if p["id"] not in defs or not form.get("lean_def"):
                continue
            nm = f"{_lean_name(p['id'])}.{_lean_name(form['id'])}"
            out += [f"/-- `{p['id']}`, form `{form['id']}`", "",
                    f"{names[p['id']]} ⇔ {form.get('name', form['id'])} -/",
                    f"def {nm} : Prop :="]
            pad = "  "
            if shape["binder"]:
                out.append("  " + shape["binder"])
                pad = "    "
            out += [f"{pad}{apply(defs[p['id']])} ↔", f"{pad}  {apply(form['lean_def'])}", ""]

    out += [f"end {ns}.Statements", ""]''',
    ),
]


def patched_json_schema(text: str, path: str) -> str:
    """The proposed change to the map's JSON schemas: `falsum` for a topic's result shape,
    `forms` for a principle."""
    if path.endswith("topic.schema.json"):
        old = """              "description": "How a principle applies inside the statement; {def} is its lean_def. Default {def}."
            }
          }
        },
        "model": {"""
        new = """              "description": "How a principle applies inside the statement; {def} is its lean_def. Default {def}."
            },
            "falsum": {
              "type": "string",
              "description": "How a result concluding False is written. Default: False."
            }
          }
        },
        "model": {"""
    else:
        old = """  "lean_def": {"""
        new = """  "forms": {
   "type": "array",
   "description": "Equivalent forms of the principle, each with a Lean definition and a certificate of its equivalence with the official form.",
   "items": {
    "type": "object",
    "additionalProperties": false,
    "required": [
     "id"
    ],
    "properties": {
     "id": {
      "type": "string"
     },
     "name": {
      "type": "string"
     },
     "statement": {
      "type": "string"
     },
     "lean_def": {
      "type": "string"
     },
     "lean_ref": {
      "type": "string"
     }
    }
   }
  },
  "lean_def": {"""
    if text.count(old) != 1:
        sys.exit(f"{path} has changed: cannot apply the proposed change")
    return text.replace(old, new)


def load_pmap(checkout: Path):
    path = checkout / "scripts" / "pmap.py"
    src = path.read_text(encoding="utf-8")
    for old, new in PMAP_CHANGES:
        if src.count(old) != 1:
            sys.exit(f"pmap.py has changed: cannot apply the proposed change at\n{old}")
        src = src.replace(old, new)
    pmap = types.ModuleType("pmap")
    pmap.__file__ = str(path)
    exec(compile(src, str(path), "exec"), pmap.__dict__)
    return pmap, src


def write_patch(checkout: Path, patched_pmap: str) -> None:
    chunks = []
    for rel, new in [("scripts/pmap.py", patched_pmap),
                     ("schema/topic.schema.json", None), ("schema/principle.schema.json", None)]:
        old = (checkout / rel).read_text(encoding="utf-8")
        if new is None:
            new = patched_json_schema(old, rel)
        chunks += difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                       f"a/{rel}", f"b/{rel}")
    (HERE / "pmap.patch").write_text("".join(chunks), encoding="utf-8")
    print("wrote map/pmap.patch")


def main() -> None:
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    checkout = Path(sys.argv[1]).resolve()
    if not (checkout / "scripts" / "pmap.py").exists() and (checkout / "logical-maps").exists():
        checkout = checkout / "logical-maps"
    pmap, patched = load_pmap(checkout)
    cfg = yaml.safe_load((HERE / "lean.yaml").read_text(encoding="utf-8"))

    original = pmap.load_topic

    def load_topic(topic_id: str) -> dict:
        data = original(topic_id)
        data["topic"]["lean_lib"] = cfg["lean_lib"]
        data["topic"]["lean"] = cfg["lean"]
        for p in data["principles"]:
            if p["id"] in cfg["lean_def"]:
                p["lean_def"] = cfg["lean_def"][p["id"]]
            if p["id"] in (cfg.get("forms") or {}):
                p["forms"] = cfg["forms"][p["id"]]
        return data

    pmap.load_topic = load_topic
    pmap.lean_lib_dir = lambda topic_id, data: (PROJECT, cfg["lean_lib"])
    path = pmap.generate_lean_statements(TOPIC)
    print(f"wrote {path.relative_to(PROJECT)}")

    data = load_topic(TOPIC)
    cov = pmap.lean_coverage(data)
    results = {r["id"] for r in data["results"]}
    stated = [i for i in cov["ready"] if i["id"] in results]
    forms = sum(len(p.get("forms") or []) for p in data["principles"])
    print(f"principles with a lean_def: {len(cov['defs'])}/{len(data['principles'])}")
    print(f"results with a statement: {len(stated)}/{len(results)}; forms: {forms}")

    if "--refs" in sys.argv:
        src = (PROJECT / "Classicism" / "Map.lean").read_text(encoding="utf-8")
        names = re.findall(r"^theorem ([a-z0-9_]+) : Statements\.\1\b", src, re.M)
        by_name = {pmap._lean_name(r): r for r in results}
        refs = {by_name[n]: f"Classicism.Map.{n}" for n in names if n in by_name}
        text = (HERE / "lean.yaml").read_text(encoding="utf-8")
        head = text[: re.search(r"^lean_ref:", text, re.M).start()]
        body = "lean_ref:\n" + "".join(f"  {k}: {refs[k]}\n" for k in sorted(refs))
        (HERE / "lean.yaml").write_text(head + body, encoding="utf-8")
        print(f"lean_ref: {len(refs)} certificates")

    if "--patch" in sys.argv:
        write_patch(checkout, patched)


if __name__ == "__main__":
    main()
