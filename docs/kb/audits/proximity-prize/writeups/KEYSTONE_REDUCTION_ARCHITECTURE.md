# Keystone reduction architecture

## Overview

The BCIKS20 Section 5 keystone is best treated as a reduction architecture rather than a monolithic
proof obligation. The current ArkLib work decomposes the route into small verified bricks plus a few
honest residual hypotheses that correspond to external or still-open mathematical content.

## Main objects

### Ingredient-D DAG

The ingredient-D route is a 28-brick dependency graph for the Hensel and coefficient-polynomial
machinery. Its purpose is to keep algebraic infrastructure separate from the list-decoding
front-door theorem.

### BetaCurveInputFin

`BetaCurveInputFin`-shaped data packages the finite inputs needed to pass from the beta recursion and
curve data into coefficient-polynomial witnesses. The important design point is that the bundle
records inputs and side conditions, not the final per-coefficient conclusion.

### Residual-ladder compression

Instead of carrying anonymous proof holes, the formalization compresses the remaining BCIKS20
Section 5 debt into named residual APIs. Each reduction theorem should say: given this precise
residual input, the downstream theorem follows.

## Why this architecture matters

This structure gives future work three useful properties:

* Locality: algebraic bricks can be audited independently.
* Honesty: external theorem debt is visible in theorem statements or named residual definitions.
* Reuse: downstream FRI/STIR/WHIR work can depend on narrowed reductions without pretending the
  keystone is fully closed.

## Current guidance

Use `docs/kb/audits/proximity-prize/CURRENT-RESIDUALIZED-TREE-2026-06-06.md` and the focused GitHub
issues as the current work index. Older campaign ledgers are provenance, not current source of
truth.
