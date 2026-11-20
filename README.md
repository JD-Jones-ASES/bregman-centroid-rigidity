# Bregman centroid rigidity

Two pooling rules are complementary when the arithmetic mean of their
outputs equals the ordinary average of the inputs. The generator of a
quasi-arithmetic rule transforms the inputs, averages them in its image,
and transforms back on the local inverse branch. Gradients of smooth
Bregman potentials are examples.

One fixed unequal input weight forces two regular generators to be affine
on a connected open subset of a real Hilbert space when the first generator
has a symmetric positive-definite derivative. This includes infinite
dimension. An equal-weight triple realizes the split `1/3, 2/3` by repeating
an input. The same conclusion follows for any fixed list of at least three
positive weights.

The hypotheses and conclusions can be inspected in [Challenge.lean](Challenge.lean).
Build the project with `lake build` using the included toolchain and manifest.
The [source comparison](Sources.md) records the classical scalar predecessors.
