#!/usr/bin/env python3
"""Generate Classicism/Statements.lean with the map's own generator.

    python3 map/generate.py <logical-maps checkout> [--refs]

Loads topics/classicism from the checkout, adds the fields of map/lean.yaml (as the map's
YAML would carry them once migrated), and runs pmap's generate_lean_statements, pointed at
this project. The output is what `pmap lean classicism` will write after the migration,
so the statements Classicism/Map.lean proves are the map's, not a copy of them.

With --refs, also fills `lean_ref` in map/lean.yaml from the certificates in
Classicism/Map.lean (a theorem named after a result id, in namespace Classicism.Map).
"""
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
TOPIC = "classicism"


def load_pmap(checkout: Path):
    spec = importlib.util.spec_from_file_location("pmap", checkout / "scripts" / "pmap.py")
    pmap = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pmap)
    return pmap


def main() -> None:
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    checkout = Path(sys.argv[1]).resolve()
    if not (checkout / "scripts" / "pmap.py").exists() and (checkout / "logical-maps").exists():
        checkout = checkout / "logical-maps"
    pmap = load_pmap(checkout)
    cfg = yaml.safe_load((HERE / "lean.yaml").read_text(encoding="utf-8"))

    original = pmap.load_topic

    def load_topic(topic_id: str) -> dict:
        data = original(topic_id)
        data["topic"]["lean_lib"] = cfg["lean_lib"]
        data["topic"]["lean"] = cfg["lean"]
        for p in data["principles"]:
            if p["id"] in cfg["lean_def"]:
                p["lean_def"] = cfg["lean_def"][p["id"]]
        return data

    pmap.load_topic = load_topic
    pmap.lean_lib_dir = lambda topic_id, data: (PROJECT, cfg["lean_lib"])
    path = pmap.generate_lean_statements(TOPIC)
    print(f"wrote {path.relative_to(PROJECT)}")

    data = load_topic(TOPIC)
    cov = pmap.lean_coverage(data)
    results = {r["id"] for r in data["results"]}
    stated = [i for i in cov["ready"] if i["id"] in results]
    print(f"principles with a lean_def: {len(cov['defs'])}/{len(data['principles'])}")
    print(f"results with a statement: {len(stated)}/{len(results)}")

    if "--refs" in sys.argv:
        src = (PROJECT / "Classicism" / "Map.lean").read_text(encoding="utf-8")
        names = re.findall(r"^theorem ([a-z0-9_]+) : Statements\.\1\b", src, re.M)
        by_name = {pmap._lean_name(r): r for r in results}
        refs = {by_name[n]: f"Classicism.Map.{n}" for n in names if n in by_name}
        text = (HERE / "lean.yaml").read_text(encoding="utf-8")
        head = text[: text.index("lean_ref:")]
        body = "lean_ref:\n" + "".join(f"  {k}: {refs[k]}\n" for k in sorted(refs))
        (HERE / "lean.yaml").write_text(head + body, encoding="utf-8")
        print(f"lean_ref: {len(refs)} certificates")


if __name__ == "__main__":
    main()
