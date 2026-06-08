---
kind: paper
bibkey: ACFY25
title: "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification (EUROCRYPT 2025)"
year: 2025
bib_source: blueprint/src/references.bib
canonical_url: https://doi.org/10.1007/978-3-031-91134-7_8
source_metadata: ../sources/ACFY25/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ProximityGap/Errors.lean
---

# ACFY25

## At A Glance

`ACFY25` is the published (EUROCRYPT 2025, LNCS) version of the WHIR paper by Arnon, Chiesa,
Fenzi, and Yogev. It is the same paper lineage as [`ACFY24`](ACFY24.md) (the ePrint version);
ArkLib cites `ACFY25` when a statement depends on the published version's lemma numbering.

## What ArkLib Uses From This Paper

- The correlated-agreement / mutual-correlated-agreement error analysis, in particular the
  Lemma 4.10 dominance bound used in the proximity-gap error development.
- Normalization and reduction steps relating `ε_mca` and `ε_ca` in the unique-decoding regime.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ProximityGap/Errors.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean)
  cites `[ACFY25, Lemma 4.10]` for the list-decoding dominance bound and the
  normalization argument behind `epsMCA_eq_epsCA_below_udr`.
- The audit page
  [`open-problems-list-decoding-and-correlated-agreement.md`](../audits/open-problems-list-decoding-and-correlated-agreement.md)
  tracks the externally-cited Lemma 4.10 dependency.

## Version Notes

- Use `ACFY24` for the ePrint version; use `ACFY25` when theorem/lemma numbering of the
  published version matters (e.g. Lemma 4.10 citations in `ProximityGap/Errors.lean`).

## Source Access

- Source metadata: [`../sources/ACFY25/metadata.yml`](../sources/ACFY25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
