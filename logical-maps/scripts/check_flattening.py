"""Check that model records in the argument format flatten exactly to what they replaced.

    python3 scripts/check_flattening.py [--ref REF] [--topic TOPIC] [--closure] [--no-lynchpins]

REF (default origin/main) is a Git revision with the records before migration. For every
model in the argument format, and every conjectured companion generated from one, the
record of the same id at REF must have the same satisfies and violates (as sets; a changed
order is reported), status, tier and model_check. A record at REF that is now neither
present nor generated is a failure. Then the topic's derived outputs must be unchanged:
the conjecture resolutions (their supporting results compared as sets, a changed order
reported), classes, every pair's status and proof, unknowns, every derived
failure's explanation in every model, problems and settled shares, and the lynchpin rows
(central questions, automatic and recorded conjectures) under every background preset, as
`build` stores them in data.json.

Any difference is a bug in the migration, not a correction to the map.

With --closure, a record may list fewer verdicts than it did, provided the engine derives the
same holds and fails from them: each model's derived holds and fails are compared instead of its
lists, and the derived outputs by their statuses and witnesses, since shorter lists change which
proof the engine shows.
"""
import argparse
import io
import json
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path
from unittest.mock import patch

import pmap

FIELDS = ("status", "tier", "model_check")


def load_at(ref: str, topic: str) -> dict:
    """The topic as it was at ref, loaded by the current loader."""
    archive = subprocess.run(["git", "-C", str(pmap.ROOT), "archive", ref, f"topics/{topic}"],
                             capture_output=True, check=True).stdout
    with tempfile.TemporaryDirectory() as tmp:
        tar = tarfile.open(fileobj=io.BytesIO(archive))
        try:
            tar.extractall(tmp, filter="data")
        except TypeError:  # Python before 3.10.12 has no extraction filters; the archive is our own
            tar.extractall(tmp)
        root = Path(tmp)
        with patch.object(pmap, "ROOT", root), patch.object(pmap, "TOPICS", root / "topics"):
            return pmap.load_topic(topic)


def derived(data: dict, lynchpins: bool) -> dict:
    pmap._PROGRESS_CACHE.clear()  # keyed on the verdicts alone, so it would serve the other tree
    an = pmap.analyse(data)
    E = an["engine"]
    # The engine explains a derived failure by the first recorded failure it reaches, so the
    # order of a violates list shows here even when its set is unchanged.
    explanations = {m["id"]: {c: E.fail_why[m["id"]][c] for c in sorted(E.fails[m["id"]])} for m in E.models}
    # What the proved records give from each model's lists, conjectured models included.
    closures = {m["id"]: {"holds": sorted(E.cl(m["satisfies"])[0] - {pmap.FALSE}),
                          "fails": sorted(c for c in E.ids if E._reaches(m["satisfies"], c, m["violates"]))}
                for m in data["models"]}
    out = {"closures": closures, "conjectures": an["conjectures"], "classes": an["classes"], "open_pairs": an["open_pairs"],
           "unknown": an["unknown"], "problems": an["problems"], "infos": an["infos"],
           "pairs": {f"{a} ⇒ {b}": v for (a, b), v in an["pair"].items()},
           "failure explanations": explanations, "progress": pmap.progress_report(data)}
    if lynchpins:
        out["lynchpins"] = pmap.lynchpin_report(data, sparse_ok=False, top=None)
    return json.loads(json.dumps(out, sort_keys=True, default=str))


def first_difference(a, b, path="") -> str:
    if type(a) is not type(b):
        return f"{path}: {str(a)[:200]} ≠ {str(b)[:200]}"
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if a.get(k) != b.get(k):
                return first_difference(a.get(k), b.get(k), f"{path}/{k}")
    if isinstance(a, list):
        if len(a) != len(b):
            return f"{path}: {len(a)} items ≠ {len(b)} items"
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                return first_difference(x, y, f"{path}[{i}]")
    return f"{path}: {str(a)[:200]} ≠ {str(b)[:200]}"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ref", default="origin/main", help="revision before the migration (default origin/main)")
    ap.add_argument("--topic", default="classicism")
    ap.add_argument("--no-lynchpins", action="store_true", help="skip the lynchpin rows (the slow part)")
    ap.add_argument("--closure", action="store_true", help="records may list fewer verdicts if the engine derives the same ones")
    a = ap.parse_args(argv)

    old, new = load_at(a.ref, a.topic), pmap.load_topic(a.topic)
    lynch = not a.no_lynchpins
    was, now = derived(old, lynch), derived(new, lynch)
    old_models, new_models = {m["id"]: m for m in old["models"]}, {m["id"]: m for m in new["models"]}
    failures = []
    flattened = [m for m in new["models"] if m.get("_source") is not None or m.get("_companion_of")]
    print(f"{a.topic}: {len(flattened)} flattened model record(s) against {a.ref}")
    for m in flattened:
        mid, before = m["id"], old_models.get(m["id"])
        kind = f"companion of {m['_companion_of']}" if m.get("_companion_of") else "model"
        if before is None:
            print(f"  {mid} ({kind}): new, nothing to compare")
            continue
        bad = []
        # With --closure, a model is compared by what the proved records give from its lists.
        derives = a.closure
        for key in ("satisfies", "violates"):
            if not derives and (set(before[key]) != set(m[key]) or len(before[key]) != len(m[key])):
                bad.append(f"{key}: lost {sorted(set(before[key]) - set(m[key]))}, gained {sorted(set(m[key]) - set(before[key]))}")
        for key in ("holds", "fails") if derives else ():
            lost = set(was["closures"][mid][key]) - set(now["closures"][mid][key])
            gained = set(now["closures"][mid][key]) - set(was["closures"][mid][key])
            if lost or gained:
                bad.append(f"derived {key}: lost {sorted(lost)}, gained {sorted(gained)}")
        for key in FIELDS:
            if before.get(key) != m.get(key):
                bad.append(f"{key}: {before.get(key)!r} ≠ {m.get(key)!r}")
        order = [k for k in ("satisfies", "violates") if before[k] != m[k] and set(before[k]) == set(m[k])]
        counts = f"{len(m['satisfies'])} holds, {len(m['violates'])} fails, {m['status']}" \
            + (f", tier {m['tier']}" if m.get("tier") else "") + (", model_check" if m.get("model_check") else "")
        if derives:
            closure = now["closures"][mid]
            print(f"  {mid} ({kind}): " + ("SAME CLOSURE" if not bad else "DIFFERENT")
                  + f" (recorded {len(before['satisfies'])} + {len(before['violates'])} before, now {counts};"
                  + f" derives {len(closure['holds'])} holds and {len(closure['fails'])} fails)")
        else:
            print(f"  {mid} ({kind}): " + ("EXACT" if not bad else "DIFFERENT") + f" ({counts})"
                  + (f"; order differs in {' and '.join(order)}" if order else ""))
        failures += [f"{mid}: {b}" for b in bad]
    for mid in old_models:
        if mid not in new_models:
            failures.append(f"{mid}: at {a.ref}, but now neither a record nor generated")
    for mid in new_models:
        if mid not in old_models and not new_models[mid].get("_source"):
            print(f"  {mid}: new list-format record")

    print("derived outputs: comparing conjectures, classes, pairs, unknowns, problems, progress"
          + ("" if a.closure else ", failure explanations") + (" and lynchpin rows (slow)" if lynch else "")
          + ("; proofs by status and witness only" if a.closure else ""))
    if a.closure:  # proofs may differ; what they prove may not
        for d in (was, now):
            del d["failure explanations"]
            for key in ("pairs", "conjectures"):
                d[key] = {k: {x: y for x, y in v.items() if x != "via"} for k, v in d[key].items()}
    for key in was:
        same = was[key] == now[key]
        reordered = []
        if not same and key == "conjectures":
            # A resolved conjecture lists its supporting results in the order of the record's own
            # satisfies and violates. Those are sets, which the arguments need not list in the old order.
            unordered = lambda d: {k: {**v, "via": sorted(v["via"])} for k, v in d.items()}
            if unordered(was[key]) == unordered(now[key]):
                same, reordered = True, [k for k in was[key] if was[key][k] != now[key][k]]
        print(f"  {key}: {'unchanged' if same else 'CHANGED'}"
              + (f" up to the order of the supporting results of {', '.join(reordered)}" if reordered else ""))
        if not same:
            failures.append(f"{key} changed at {first_difference(was[key], now[key], key)}")
    for f in failures:
        print(f"FAIL {f}")
    print(("PASS: every flattened record derives what it did, and every derived output is unchanged." if a.closure
           else "PASS: every flattened record and every derived output is unchanged.") if not failures
          else f"{len(failures)} failure(s).")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
