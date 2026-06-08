# C3.8 off-lattice repair note

## Claim

The off-lattice use of the MS77/Stirling-style volume estimate in the C3.8 route is not sound as
stated. A direct countermodel at `q = 2`, `n = 4`, and `delta = 0.49` shows that the real-radius
reading can cross an integer-radius boundary that the discrete Hamming ball count does not cross.

## Diagnosis

The formal issue is not the asymptotic volume heuristic itself. The failure is the missing
integer-radius bridge:

* Hamming balls count words at integer distance.
* The prose route reasons with a real radius.
* The claimed inequality is applied before proving that rounding preserves the required side
  conditions.

This makes the route brittle exactly near boundary values. The small `q = 2`, `n = 4`,
`delta = 0.49` instance is enough to expose the mismatch.

## Repair

The honest repair is to replace the off-lattice step by an integer-radius statement:

1. Define the radius as `r = floor (delta * n)` or another explicit integer convention.
2. State every ball-size inequality in terms of that integer `r`.
3. Port a Robbins-style factorial/Stirling bound only after proving the rounding side conditions.
4. Keep the finite exceptional cases as explicit arithmetic checks rather than absorbing them into
   the asymptotic statement.

## Status

This is a statement-repair note. It does not claim the original C3.8 proof route is closed; it
identifies the exact bridge that must be formalized before any volume-bound argument can be reused.
