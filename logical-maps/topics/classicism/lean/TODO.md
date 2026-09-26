# Small, non-urgent cleanups

Things worth doing the next time the whole project is being rebuilt anyway. None of them
changes a statement or a proof; each touches enough files that it is not worth a rebuild
of its own. The agenda proper is in `HANDOFF.md`, §5.

- **Rename `boxImp` to `incl`.** `boxImp` names `λXY. ∀z̄. Xz̄ → Yz̄`, the pointwise
  implication whose whole point is that it does *not* begin with a box; the name misleads.
  Cian's suggestion (26 September 2026): `incl`, for inclusion. The rename runs through every
  layer, since the name is a field of `Rel` (`Classicism/Core.lean`) and everything reads
  through it: the shallow library (`Order`, `Pointwise`, `Comprehension`, the `boxImp_*`
  lemmas), the strict mirror (`SRel.boxImp`, `SPointwise`), the syntax (`Term.boxImpR`,
  `Term.unfoldBoxImp`, `RTy.boxImpD`), the semantics (`boxImpRead`, `truncate_boxImpRead`),
  the translator, and `Results/`. About 290 occurrences in 24 files. Rename the derived
  lemma names with it (`incl_trans`, `incl_of_coext`, …), and `boxImpR`/`boxImpD`/`boxImpRead`
  to match. Docstrings that gloss the operation as `⊑` can stay.
