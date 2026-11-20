# Proof of the centroid classification

Let $U$ be a connected open subset of a real Hilbert space and let $F,G$ have boundedly invertible derivatives there. Assume that $DF(x)$ is self-adjoint and positive definite at each $x$. If $F=\nabla\phi$ this is the positive Hessian condition. The second generator can be any local diffeomorphism of the required smoothness.

For binary input weight $w$ at $y$, the two centroids $u,v$ satisfy

$$
F(u)=(1-w)F(x)+wF(y),\qquad G(v)=(1-w)G(x)+wG(y).
$$

The inverse function theorem supplies these centroids near every diagonal point $(p,p)$. Their images under the assigned local inverse branches tend to $p$. This puts both centroids in any prescribed neighborhood once the endpoints are sufficiently close. The `local_centroid_existence` theorem records this explicitly. Local balance is the identity $u+v=2((1-w)x+wy)$ for these points. The [formal statement](Challenge.lean) defines the local and finite-family versions.

## Unequal input weights

Write $A=DF$, $B=DG$. Differentiate balance with respect to each endpoint, cancel its nonzero weight and subtract. The resulting endpoint equation is

$$
A(u)^{-1}(A(y)-A(x))+B(v)^{-1}(B(y)-B(x))=0.
$$

Take $x=p$, $y=p+th$. Dividing by $t$ and taking the limit gives

$$
K_h=A^{-1}\partial_h A=-B^{-1}\partial_hB.
$$

Swapping the endpoints also gives balance with input weight $1-w$. At both weights the endpoint differences are identical. Along the chosen line the velocity of either centroid at $t=0$ equals the input weight times $h$. Differentiating the inverse Jacobians and subtracting the two endpoint equations gives the second-order coefficient $-2(2w-1)K_h^2$. Thus $K_h^2=0$ whenever $w\ne 1/2$.

Use $\langle x,y\rangle_A=\langle A(p)x,y\rangle$. Since $AK_h=\partial_h A$ is self-adjoint in the original inner product, $K_h$ is self-adjoint in this one. For every $z$ we have $\langle K_hz,K_hz\rangle_A=\langle z,K_h^2z\rangle_A=0$. Positivity gives $K_h=0$. Both Jacobians are constant on the connected domain and both generators are affine. This argument needs $C^2$ regularity. The operator identities preceding the positivity step also hold on real Banach spaces. [Endpoint proof](CentroidRigidity/Endpoints.lean) · [Unequal weights](CentroidRigidity/Unequal.lean)

In a triple $(x,x,y)$ the second distinct prediction gets weight $1/3$. In any list of at least three positive weights summing to one, some weight is different from $1/2$. Put $y$ at that index and $x$ at every other index. Conversely affine generators preserve every finite weighted average with weight sum one. This proves `three_input_centroids`, `weighted_family_centroids` and `arithmetic_predictions_of_triples`. The last result identifies the two individual outputs even for a later, different list of weights. [Finite families](CentroidRigidity/Families.lean) · [Arithmetic predictions](CentroidRigidity/Arithmetic.lean)

For a potential with gradient $F(z)=Lz+b$, the proof integrates this gradient on the connected open domain. With the gradient at $x$ subtracted, the divergence is

$$
D_\phi(z,x)=\phi(z)-\phi(x)-\langle F(x),z-x\rangle
           =\tfrac12\langle L(z-x),z-x\rangle.
$$

The constant $L$ is symmetric positive definite. The second loss has its own operator. The argument compares derivatives of the two sides on the entire domain and works when a straight segment leaves that domain. [Loss theorem](CentroidRigidity/Loss.lean)

## What survives at half weight

Assume $C^3$ generators. Fix $p,h$ and set $C(s)=K_h(p+sh)$, $C=C(0)$ and $D=C'(0)$. Normalize the endpoint Jacobians by multiplying on the left by their inverse at $p$ and call the results $P(s),Q(s)$. They satisfy

$$
P'=PC(s),\qquad Q'=-QC(s),\qquad P(0)=Q(0)=I.
$$

On the symmetric chord $p-th,p+th$ the two centers are related by reflection about $p$. Each center moves by $O(t^2)$. The product of the two normalized center factors, with one inverted, has zero first derivative as a function of the center at $p$ because the logarithmic Jacobians are opposite. Their relative discrepancy along the chord is therefore $o(t^2)$. Multiplying by the endpoint differences, which are $O(t)$, gives

$$
P(t)-P(-t)+Q(t)-Q(-t)=o(t^3).
$$

Meanwhile $P-Q=2sC+s^2D+o(s^2)$. Multiplication on the right by $C(s)=C+sD+o(s)$ gives

$$
(P+Q)'=2sC^2+s^2(2CD+DC)+o(s^2).
$$

Integrating the derivative on the symmetric chord and comparing the cubic coefficients gives $2CD+DC=0$. The proof uses a norm estimate for the integrated remainder and preserves the order of the operator products. Its differentiability assumptions cover singular $C$. [Remainder estimates](CentroidRigidity/Peano.lean) · [Chord comparison](CentroidRigidity/ChordComparison.lean)

Both $C$ and $D$ are self-adjoint in the inner product at $p$. For $D$, differentiate $A'=AC(s)$ once more to get $A''=A(C^2+D)$. Taking the adjoint of the cubic identity gives $2DC+CD=0$, so $CD=DC=0$. This holds at every nearby point of the line. It implies $(C(s)^2)'=0$.

Here is the step that extends constancy to infinite dimension. Fix $z$ and set $b=Dz$. Since $C(0)b=0$ and $C(s)^2$ is locally constant, $C(s)^2b=0$ for every nearby $s$. Positive self-adjointness in the inner product at that point gives $C(s)b=0$. Differentiate this last identity at zero to obtain $D^2z=0$. Apply positive self-adjointness once more, this time to $D$, to get $Dz=0$. Hence $\partial_h K_h=0$ for every $h$. [Hilbert-space argument](CentroidRigidity/Metric.lean) · [Directional stationarity](CentroidRigidity/Stationarity.lean)

For constant directions $a,b$, commute the mixed partials of $A$ and $B$. The two resulting equations have opposite derivative terms and identical commutators. Consequently $[K_a,K_b]=0$ and $\partial_aK_b=\partial_bK_a$. Polarizing $\partial_hK_h=0$ gives $\partial_aK_b=0$ for all directions. Connectedness makes each $K_b$ constant across the domain. This is `half_weight_operator`. [Mixed derivatives](CentroidRigidity/FlatField.lean)

## A single basis and its predictions

In finite dimension, diagonalize the commuting operators in the fixed inner product at a chosen base point $p$. Their joint eigenspaces span the space. Choose one basis $e_i$ of joint eigenvectors. Symmetry of $D^2F$ gives $K_{e_i}e_j=K_{e_j}e_i$. For distinct indices, this vector belongs to two distinct basis lines, so it is zero. Write $K_{e_i}e_i=\lambda_i e_i$. For $h=\sum h_i e_i$ it follows that $K_he_i=\lambda_i h_i e_i$. No simplicity assumption on the eigenvalues is needed. [Common axes](CentroidRigidity/Spectral.lean)

Write $x=p+\sum z_i e_i$. The derivative in every direction of $e^{-\lambda_i z_i}A(x)e_i$ is zero. The sign for $B$ is reversed. Integrating the columns gives

$$
F(x)=F(p)+\sum_i s_{\lambda_i}(z_i)A(p)e_i,\qquad
G(x)=G(p)+\sum_i s_{-\lambda_i}(z_i)B(p)e_i,
$$

where $s_0(t)=t$ and $s_\lambda(t)=(e^{\lambda t}-1)/\lambda$ for $\lambda\ne0$. Each scalar chart has value zero and derivative one at zero. The binary output formulas now follow by applying the basis coordinates and inverting the scalar charts. For the converse, the identity
$(e^{\lambda a}+e^{\lambda b})=e^{\lambda(a+b)}(e^{-\lambda a}+e^{-\lambda b})$
shows that the two scalar outputs sum to $a+b$. Summation over the common basis proves actual local balance. This establishes `binary_generator_classification` and `binary_prediction_formulas`. A choice of discrete axes is asserted only in finite dimension. [Integration](CentroidRigidity/Integration.lean) · [Classification](CentroidRigidity/Classification.lean) · [Prediction formulas](CentroidRigidity/Predictions.lean)

## Individual triples and the gradient assumption

For a triple with mean $m$, put $a_i=e^{\lambda(x_i-m)}$. Their product is one. When $\lambda\ne0$, the positive and negative exponential pools balance exactly when $\sum a_i=\sum 1/a_i$. Subtracting and using the product constraint factors the difference as $(a_1-1)(a_2-1)(a_3-1)$. Thus at least one input must equal $m$. A single pair $(-\log2,\log2)$ yields two distinct answers $\log(5/4)$ and $-\log(5/4)$, both different from its midpoint. The scalar generator equation, the triple criterion and both binary witness statements are compared declarations. [Scalar examples](CentroidRigidity/Examples.lean)

For the planar shears $(s,r)\mapsto(s,r\pm f(s))$, each second centroid coordinate is $\bar r\pm(\sum_iw_i f(s_i)-f(\bar s))$. The displacements cancel for every arity. For $f(s)=s^2$ they are opposite variances and can be nonzero. The example admits strictly monotone restrictions and typically has nonsymmetric Jacobians. It explains how a nonzero square-zero operator can survive when the metric step is unavailable. The formal algebra even allows arbitrary finite real weights. [Shear identity](CentroidRigidity/Shear.lean) · [Okamura, Theorem 4.2](https://arxiv.org/html/2609.11102v1#S4)
