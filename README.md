# Operational vs Semantic Equality

## A Machine-Checked Separation of Completion and Finite Attainment in the Gregory-Leibniz Construction of Pi

## Publication and DOI

**Zenodo record:** https://zenodo.org/records/22054459  
**DOI:** https://doi.org/10.5281/zenodo.22054459  
**Version:** 1.5.3  
**Publication date:** 2026-08-22  
**Paper license:** CC BY 4.0

Recommended citation:

> Eduardo Martinez Dammroze (2026). *Operational vs Semantic Equality: A Machine-Checked Separation of Completion and Finite Attainment in the Gregory-Leibniz Construction of Pi*. Version 1.5.3. Zenodo. https://doi.org/10.5281/zenodo.22054459

The GitHub repository and the exact `v1.5.3` release are recorded in Zenodo as supplementary formal-source identifiers.

### Headline

**Completion is not a finite-witness extractor.**

The claim is deliberately narrower than "pi does not close."

The completed classical Euclidean identity

    G_r(2*pi*r) = G_r(0)

is granted.

The finite core proves that the paper's local full-tail zero
criterion does not universally entail a finite exact-zero witness.

The classical adversarial layer additionally proves:

    Real.mk(G) = pi

while:

    for every finite n, G_n != pi

and, for nonzero radius, no nonempty finite Gregory traversal stage
returns exactly to its starting point.

The publication does not claim inconsistency of classical real
analysis, nonexistence of traditional real pi, or failure of the
completed Euclidean circle to close.

Formal inventory:

- 62 finite-core Lean modules
- 8 classical adversarial Lean modules
- 70 Lean modules total
- NPi is not used

Final TeX SHA-256:

    7a0f939392ff82cce0c1220440fced23110396d50298a3c24b21929cc1b1d3e9

Final PDF SHA-256:

    b62389205b3760a21a5d768aaa6eee27f41d26ba5f2eacdcdfb6da9acaf6986c
