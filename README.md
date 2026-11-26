# Positive-D regional completion

This directory proves the real secant estimates needed for regional row 2,
`1/4 ≤ F < 1` and `D > 0`, with a bound of one distinct isolated critical
energy. The final parameter-only statement is
`LeanVerification.PositiveDCompletion.full_regional_row2` in
`CompleteRow2.lean`.

**Current verification status:** the actual physical transport, the two strict
secant cones, the upper certificates, and all source and pole identities have
passed Lean. The remaining lower certificates and final regional
assembly are still being checked. The row is not yet a checked full export.

## Proof structure

`SignedQuadratic`, `PhysicalSheet`, and `SignedTransport` identify the actual
real branch for positive `D`; they do not use the positive mixture branch from
the reflected wedge. `HyperbolicBounds`, `LowerCone`, and `SecantGeometry` prove
the strict interior correlations for both ranges of the normalized exponent.
`PhysicalModel`, `ActualCurvatureJet`, and `PhysicalConeSigns` connect the exact
rational jets and all denominator signs to the actual two turning points.

`SourceNumerators` and `PoleValues` provide the complete source and pole
identities. `PolynomialComparison` reduces the required curvature implication
to ten finite signs on each secant cone. The upper and lower certificate chains
prove these signs with respectively 8,584 and 59,167 positive integer Bernstein
coefficients. `PhysicalConclusion` applies the checked width and Abel-period
transfer, including its identically zero input alternative. `HalfSeam` and the
frozen quarter-region theorem cover the two exceptional parameter slices.

The mathematical details and exact coordinate changes are in
`PROOF_NOTES.tex`.

## Serial build

Run the following from the project root before building the full aggregate:

```sh
python LeanVerification/PositiveDCompletion/build_serial.py --lean-bin-dir /path/to/lean-4.19.0-linux/bin
lake build LeanVerification
```

The helper reads the imports of `CompleteRow2`, checks that every proof module
in this directory is reachable, and builds that closure in dependency order.
It runs one Lake target process at a time and stops on the first failure.
Per-target logs and source hashes are recorded under
`logs/positive_d_serial/`. Existing valid Lake artifacts are reused. The
`--list` option prints the order without invoking Lean or Lake, and
`--lean-bin-dir` can be omitted when the required toolchain is already on
`PATH`.

## Exact data and regeneration

The three JSON files in `data/` contain the complete integer inputs. They do
not depend on temporary symbolic caches. Python 3 and SymPy are sufficient for
the following diagnostics:

```sh
python LeanVerification/PositiveDCompletion/reproduce_generated.py --check
python LeanVerification/PositiveDCompletion/verify_exact_data.py
```

The first command generates all 431 generated proof modules in a separate
temporary directory and compares them byte for byte with the checked sources.
It never overwrites those sources. Supply `--output DIRECTORY` to retain the
regenerated files.

The second command independently checks the full Bernstein identities, every
lower homogeneous coordinate core, all twelve source coefficient identities,
all twelve pole coefficient identities, and the four pole comparisons with
sparse integer arithmetic. It also verifies the strict positivity of all
67,751 Bernstein coefficients. Supply `--report FILE.json` to save its result.
These diagnostics supplement the Lean proof; they are not trusted proof
oracles.

The generation scripts keep large certificates in separate data, coordinate,
block, and coefficient modules. Numeric powers in the large generated
expressions have explicit natural-number types to keep elaboration bounded.
The ungenerated analytic and generic algebra modules are ordinary Lean source
files included directly in this directory.
