# Bregman centroid rigidity

Two prediction rules can disagree on every distinct pair and still have their two answers average to the ordinary midpoint. Requiring the corresponding identity on every nearby triple forces each rule to return the arithmetic average. Three predictions suffice even when two of them are copies of the same prediction.

A quasi-arithmetic rule with generator $F$ sends the inputs through $F$, takes a weighted arithmetic average and uses a local inverse to return to the prediction space. A Bregman loss with potential $\phi$ has this rule with $F=\nabla\phi$ when the candidate prediction is the **first** argument of the divergence. Its centroid solves $\nabla\phi(u)=\sum_i w_i\nabla\phi(x_i)$. An open convex domain and a positive-definite Hessian give a unique minimizer whenever that equation has a solution. The formal statements use the local generator equations, so they also apply on connected open domains.

## The results

* **Unequal input weights.** On a connected open subset of a real Hilbert space, take two $C^2$ generators with boundedly invertible derivatives. Suppose the first derivative $DF$ is symmetric positive definite at every point. If the centroids at one fixed input weight $0<w<1$, $w\ne 1/2$, have average $(1-w)x+wy$ for all nearby pairs, both generators are affine. Dimension can be infinite. Only the first generator needs the positivity and symmetry assumption.
* **Three or more inputs.** The triple $(x,x,y)$ gives $y$ weight $1/3$. Every fixed list of at least three positive weights summing to one also has an entry different from $1/2$. For every such list, local balance is equivalent to both generators being affine. After triple balance, each actual centroid of any finite normalized weighted family is its arithmetic prediction. For two gradients with positive-definite derivatives, each Bregman loss is a squared Mahalanobis distance in its own fixed quadratic form.
* **Equally weighted pairs.** For $C^3$ generators the logarithmic derivative operators of $DF$ are constant and commute, including in infinite dimension. In finite dimension, on one fixed basis throughout the domain, the two generators split into independent scalar directions. On axis $i$ their averages have parameters $\lambda_i$ and $-\lambda_i$. Both the necessity and the converse are formalized, including the generator formulas and the values of the actual predictions.

For parameter $\lambda\ne0$ the scalar rule is

$$
m_\lambda(a,b)=\frac{1}{\lambda}\log\!\left(\frac{e^{\lambda a}+e^{\lambda b}}{2}\right).
$$

At $\lambda=0$ it is $(a+b)/2$. For example, the convex loss potentials $e^x$ and $e^{-x}$ pool $m-h,m+h$ to $m+\log\cosh h$ and $m-\log\cosh h$. On a nonlinear axis three inputs balance precisely when one equals their arithmetic mean. Thus every equally spaced triple passes. A triple with two copies of one value and a different third value exposes the nonlinearity.

The scalar classification has classical predecessors. The vector argument derives common coordinates even when the original features interact. Okamura’s shear examples explain the role of the gradient assumption. Priority of the full vector statement remains open. [Mathematical sources](Sources.md)

## Proof and verification

The [proof guide](Proof.md) derives the operator identities, the Hilbert-space constancy argument, the finite-dimensional classification and the loss formula. The [formal statement](Challenge.lean) contains the definitions and the 14 compared theorems. The [solution](Solution.lean) connects each statement to its proof.

With the pinned toolchain and Mathlib dependency, run the following commands from the repository root. The symbolic replay uses SymPy 1.14.0.

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/check_contracts.py
python3 scripts/exact_replay.py
```

The [Linux workflow](.github/workflows/verify.yml) builds from a fresh checkout, runs the symbolic replay and mutation controls, then runs sandboxed Comparator with Lean, NanoDa and con-ron. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The [metadata workflow](.github/workflows/metadata.yml) checks the v0.4 schema, the official provenance parser and the submission-form parser. Exact results are recorded per commit in [GitHub Actions](https://github.com/JD-Jones-ASES/bregman-centroid-rigidity/actions).

JD Jones directed the investigation and maintains the repository. GPT-6.2 Astra in OpenAI Codex developed the mathematical argument, Lean proofs and exact checks. Independent human specialist review and mathematical priority remain open. The repository uses the [MIT license](LICENSE).
