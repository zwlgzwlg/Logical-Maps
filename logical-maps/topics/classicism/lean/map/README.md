# The Lean side of the map

A draft of how this project plugs into the Logical Map (`zwlgzwlg/Logical-Maps`,
`topics/classicism`), in the map's own terms. Nothing here changes the map; it is what
the map's YAML and build would carry once the project moves there.

## How the map certifies a result

The map already has a Lean mechanism (`scripts/pmap.py`, used by the Unbounded Utility
topic):

- each principle names a Lean term in `lean_def`;
- `pmap lean` writes `<lib>/Statements.lean`, one `Prop` per result, assembled from the
  result's premises and conclusion in the shape the topic declares under `lean:`;
- a result's `certificate.lean_ref` names a proof, and `pmap lean-check --update` marks the
  result `verified` only if that proof has the generated type and rests on no axiom beyond
  `propext`, `Classical.choice` and `Quot.sound`.

So the official certificate of a result is the declaration its `lean_ref` names, checked
against a statement the map writes itself.

## What is here

| file | what it is |
| --- | --- |
| `lean.yaml` | The fields the map would carry: `lean_lib` and `lean` (for `topic.yaml`), a `lean_def` for each of the 76 principles formalized here, and a `lean_ref` for each of the 202 results certified. |
| `generate.py` | Runs the map's own generator on a checkout of the map with these fields added, writing `Classicism/Statements.lean`; with `--refs`, fills `lean_ref` from `Classicism/Map.lean`. |
| `index.json` | For each certified result: its certificate (file, lines, axioms) and the declarations a reader wants, the proofs (file, lines). Written by `scripts/MapIndex.lean`. |

and, in the library:

| file | what it is |
| --- | --- |
| `Classicism/Statements.lean` | The generated statements (216 of the 270 results, those whose principles all have a `lean_def`, and 3 models). Not edited by hand. |
| `Classicism/Map.lean` | One certificate per result proved, named by its id, of the generated type: the `lean_ref`s. Each is one line citing the proof. |
| `Classicism/Tools/MapIndex.lean` | `#classicism_map_index`, which writes `index.json`. |

To regenerate, from `Cian/`:

    python3 map/generate.py <logical-maps checkout> --refs   # needs pyyaml, jsonschema
    lake build
    lake env lean scripts/MapIndex.lean

## The shape of a statement

    ∀ {Sig} (Ax : AxiomSet Sig), Consistent Ax →
      Entails Ax A₁ → … → Entails Ax Aₙ → Entails Ax C        (or → False)

For every signature and every consistent schema `Ax` over it, if `Ax` entails each premise,
it entails the conclusion. This is equivalent to the entailment `A₁ ∪ … ∪ Aₙ ⟹ C`, and for
an incompatibility to the inconsistency of the premises, so the generator's `False`
conclusion needs no special case. Each `lean_def` is a schema: a principle's schema read in
the signature (`AxiomSet.ofPure P.Barcan.schema`), Actual Profile's list form (the map
states it for tuples), or a sentence schema, at the signature for the signature-relative
principles (`AxiomSet.noContingency _`). Quantifying over signatures is what lets the seven
signature results be stated at all; for a pure result it costs nothing, since a pure
derivation is one in every signature.

The certificate is the object-language entailment, not the shallow proof. The claim is
about `C`, and the map's axiom list is harmless elsewhere but not here: `propext` is the
Fregean Axiom, so a shallow proof passing that check would show nothing about `C`. The
entailments use `propext` and `Quot.sound` only as reasoning about syntax.

## What a map viewer should see

Today the viewer's "lean" link is the root of the topic's Lean directory for every result.
With `index.json` it can link each result to its proof:

- **Proof**, the first entry of `proofs`: the shallow proof in `Results/Records.lean`, at one
  argument type for a result at every arity, or the metalogical proof in
  `Results/SentenceSchemas/`;
- **At every arity**, when there is a second entry: the theorem in `Results/Arity.lean`;
- **Certificate**: the line in `Classicism/Map.lean`, with its axioms.

A link is a file and a line range, made into a URL by the map's build (a GitHub blob at a
pinned commit, `#L2145-L2160`, or a rendered source page with line anchors). This needs a
small change to `pmap` and `viewer/template.html` in the map repository.

## Open points

- **Axioms.** 193 certificates rest on `propext` and `Quot.sound` only, and six more also
  on `Classical.choice` (the models), all within the map's list. Three rest also on
  `Classicism.e` and `e_exists`,
  through the consistency facts from the model in `Prop`, which needs an individual:
  `maximalist-distinctness-incompatible-with-nd`,
  `possibility-and-no-pure-contingency-incompatible` and
  `pure-b-and-pure-possibility-incompatible`. `lean-check` would refuse those three until
  the map's list allows the two, or the model is built on a type known to be inhabited.
- **Coverage.** 21 of the map's 97 principles have no `lean_def` (the Infinity
  principles, Witnessed Possibility and its kin, Separated Structure, the Necessity of
  Arithmetic and others), so 54 results have no statement. Of the 216 stated, 14 are not
  yet proved here.
- **Models.** Three of the map's models get statements (`∃` a consistent `Ax` entailing what
  the model satisfies and not what it violates); none is certified yet.
- **Mathlib.** `lean-check` runs `lake build` on the topic's Lean directory; this project
  needs Mathlib (for the model theory only).
