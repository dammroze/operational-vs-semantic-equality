# Changelog

All notable publication and formal-development changes are recorded
here.

The project follows immutable-release provenance: frozen releases are
not rewritten after promotion.

## [1.5.3] - Semantic

### Scope-Hardened Publication Final

Canonical publication title:

**Operational**

Canonical headline:

**Completion is not a finite-witness extractor.**

The final publication framing makes explicit that the machine-checked
counterexample concerns the implication from semantic completion or
semantic equality, by itself, to a finite terminal witness in the
generating process.

It does not claim:

- inconsistency of classical real analysis;
- nonexistence of traditional real pi;
- failure of completed classical Euclidean closure;
- that convergence-versus-attainment is itself a new mathematical
  observation;
- that a richer formalism could not explicitly carry additional finite
  witness data.

### Added in the V1.5.3 formal chain

- finite Euclidean return-to-start barrier for nonempty finite
  Gregory-generated stages at nonzero radius;
- explicit host-metatheory/object-level-finiteness boundary;
- concrete Mathlib completion provenance;
- simultaneous formal comparison

  `Real.mk(G) = pi`

  with

  `for every finite n, G_n != pi`.

### Publication hardening

- title changed from the earlier ultrafinitary/pi-centered framing to
  an operational-versus-semantic equality framing;
- abstract foregrounds the exact negative-scope claims;
- Introduction begins with the foundational completion/attainment
  distinction;
- Conclusion states the surviving theorem scope explicitly;
- machine-style `FINAL_STATUS` flags are identified as scoped audit
  records rather than global metaphysical assertions;
- Mathlib dependencies `propext`, `Classical.choice`, and `Quot.sound`
  are reported as external dependencies of the classical comparison
  layer, not identified as a theorem-level unique source of actual
  infinity.

### Formal inventory

- 62 finite-core Lean modules;
- 8 classical adversarial bridge modules;
- 70 active Lean modules total;
- no Lean source modified by the final publication-framing passes;
- NPi is not used in this publication.

### Canonical publication hashes

TeX SHA-256:

`Equality:`

PDF SHA-256:

`A`

## [1.5.2]

Foundational publication baseline preceding the V1.5.3 adversarial
hardening.

V1.5.2 introduced no new formal theorem. Its role was publication
integration, scope control, and consolidation of the existing formal
chain before the V1.5.3 additions.

## Earlier development

Earlier frozen checkpoints remain preserved in the project's
`FROZEN_CHECKPOINTS` provenance chain. They are historical
checkpoints, not the current canonical publication.
