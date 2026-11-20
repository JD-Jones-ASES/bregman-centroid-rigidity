"""Replay the algebra and controls in the centroid balance proof using SymPy."""

from itertools import combinations_with_replacement

import sympy as sp


def require(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def check_scalar_means() -> None:
    a, b, u = sp.symbols("a b u", positive=True)
    upper = (a + b) / 2
    lower = 2 / (1 / a + 1 / b)
    require(sp.cancel(upper * lower - a * b) == 0, "opposite exponential binary generators")
    example = {a: 1, b: 4}
    require(upper.subs(example) == sp.Rational(5, 2), "upper centroid on (0, log 4)")
    require(lower.subs(example) == sp.Rational(8, 5), "lower centroid on (0, log 4)")

    # Inputs (0, 0, t), u = exp(lambda*t/3). Work in exponential coordinates.
    triple = (2 + u**3) / (2 + u**-3)
    difference = sp.cancel(triple - u**2)
    expected = u**2 * (u - 1)**3 * (u + 1) / (2*u**3 + 1)
    require(sp.cancel(difference - expected) == 0, "factor the ternary defect")
    require(triple.subs(u, 2) == sp.Rational(80, 17), "exact unequal triple")
    require(difference.subs(u, 1) == 0, "coincident triple")

    # Exponentiating the three centered inputs gives a*b*c = 1.
    c = 1 / (a * b)
    centered_difference = a + b + c - 1 / a - 1 / b - 1 / c
    product = (a - 1) * (b - 1) * (c - 1)
    require(sp.cancel(centered_difference - product) == 0, "all balanced scalar triples")


def check_reciprocal_derivatives() -> None:
    # F(x)=x+x²/2, G(x)=log(1+x), x>-1. Their derivatives multiply to one.
    # Invert the two coordinate averages explicitly, independently of the jet proof.
    t, w = sp.symbols("t w", real=True)
    weighted = sp.sqrt(1 + w*(2*t + t**2)) + (1 + t)**w - 2 - 2*w*t
    cubic = sp.diff(weighted, t, 3).subs(t, 0) / 6
    require(sp.factor(cubic - w*(1-w)*(1-2*w)/3) == 0, "direct unequal-weight defect")
    symmetric = sp.sqrt(1+t**2) + sp.sqrt(1-t**2) - 2
    require(sp.diff(symmetric, t, 4).subs(t, 0) / 24 == -sp.Rational(1, 4),
            "opposite logarithmic derivatives alone do not give binary balance")


def check_matrix_coefficients() -> None:
    # Free noncommuting symbols keep track of product order in arbitrary dimension.
    t, w = sp.symbols("t w", real=True)
    K, K1, K2, shift = sp.symbols("K K1 K2 shift", commutative=False)

    # Center Jacobian inverse times endpoint Jacobian difference, for each sign.
    # At weights w and 1-w the same endpoint difference occurs in both equations.
    def swapped_inverse_term(sign: int):
        center_w = 1 - sign*w*t*K
        center_other = 1 - sign*(1 - w)*t*K
        return (center_w - center_other) * (sign*t*K)

    swap = sp.expand(swapped_inverse_term(1) + swapped_inverse_term(-1))
    require(sp.expand(swap + 2*(2*w - 1)*t**2*K**2) == 0, "swapped weights")
    require(swap.subs(w, sp.Rational(1, 2)) == 0, "equal weights are exceptional")
    require(swap.subs(w, sp.Rational(1, 3)) != 0, "repeated triple detects the square")

    # Independent coefficient calculation. Solve U' = sign * U * K(t) in
    # noncommuting power series, allowing an arbitrary quadratic coefficient.
    # The proof needs only differentiable K(t) and uses an integral instead.
    def signed_chord(sign: int):
        field = (K, K1, K2)
        coeff = [sp.Integer(1)]
        for degree in range(3):
            product = sum(coeff[i] * field[degree-i] for i in range(degree+1))
            coeff.append(sp.expand(sign * product / (degree + 1)))
        return 2 * (t*coeff[1] + t**3*coeff[3])

    plus, minus = signed_chord(1), signed_chord(-1)
    # Opposite center displacements and opposite generators yield the SAME shift.
    center = 1 - t**2*shift/2
    cubic = sp.expand(center*plus + center*minus).coeff(t, 3)
    expected = sp.Rational(2, 3) * (2*K*K1 + K1*K)
    require(sp.expand(cubic - expected) == 0, "ordered cubic coefficient")
    require(sp.expand(cubic - 2*K*K1) != 0, "detect accidental commutation")
    wrong_sign = sp.expand(center*plus + (1 + t**2*shift/2)*minus).coeff(t, 3)
    require(sp.expand(cubic - wrong_sign) != 0, "detect reversed center shift")


def check_mixed_coordinates() -> None:
    # z = S*x, potentials exp(±z1) + exp(∓2*z2)/4 + z3²/2.
    # State (a,b,c) encodes (exp(z1), exp(-2*z2), z3) exactly.
    S = sp.Matrix([[1, 1, 0], [0, 1, 1], [1, 0, 1]])
    S_inv_t = S.T.inv()
    states = [tuple(map(sp.Rational, row)) for row in
              [(1, 1, 0), (4, 3, -1), (8, 1, 2), (2, 9, 0)]]

    def gradient(state, sign):
        a, b, c = state
        return S.T * sp.Matrix([sign*a**sign, -sign*b**sign/2, c])

    def inverse_gradient(value, sign):
        a, b, c = S_inv_t * value
        return ((sign*a)**sign, (-2*sign*b)**sign, c)

    def mean(points, sign):
        total = sum((gradient(point, sign) for point in points), sp.zeros(3, 1))
        return inverse_gradient(total / len(points), sign)

    metric = S.T * S
    for a, b, c in states:
        for sign in (-1, 1):
            require(inverse_gradient(gradient((a, b, c), sign), sign) == (a, b, c),
                    "gradient and inverse round trip")
        H = S.T * sp.diag(a, b, 1) * S
        J = S.T * sp.diag(1/a, 1/b, 1) * S
        require(metric * H.inv() * metric == J, "constant Hessian geometric mean")
    H = S.T * sp.diag(4, 3, 1) * S
    J = S.T * sp.diag(sp.Rational(1, 4), sp.Rational(1, 3), 1) * S
    require(H*J != J*H, "example must include noncommuting Hessians")

    for x, y in combinations_with_replacement(states, 2):
        plus, minus = mean((x, y), 1), mean((x, y), -1)
        for i in (0, 1):
            require(plus[i]*minus[i] == x[i]*y[i], "binary exponential coordinate")
        require(plus[2]+minus[2] == x[2]+y[2], "binary linear coordinate")
    x, y = states[0], states[2]
    plus, minus = mean((x, x, y), 1), mean((x, x, y), -1)
    require((plus[0]*minus[0])**3 != (x[0]**2*y[0])**2, "mixed triple must fail")


def check_shear_control() -> None:
    # Okamura's shear construction with q(x)=x² on the strip |x|<1.
    # Both generators are smooth and strictly monotone there.
    x_values = sp.symbols("x0:3", real=True)
    y_values = sp.symbols("y0:3", real=True)
    p, q = sp.symbols("p q", real=True)
    weights = (p, q, 1 - p - q)
    avg_x = sum(w * x for w, x in zip(weights, x_values))
    avg_y = sum(w * y for w, y in zip(weights, y_values))

    def output_y(sign):
        transformed = sum(
            w * (y + sign * x**2) for w, x, y in zip(weights, x_values, y_values)
        )
        return transformed - sign * avg_x**2

    require(sp.expand(output_y(1) + output_y(-1) - 2 * avg_y) == 0, "shear balance")
    variance = sum(w * (x - avg_x)**2 for w, x in zip(weights, x_values))
    require(sp.expand(output_y(1) - avg_y - variance) == 0, "positive shear displacement")
    third = sp.Rational(1, 3)
    half = sp.Rational(1, 2)
    example = {p: third, q: third, x_values[0]: -half, x_values[1]: 0, x_values[2]: half}
    require(variance.subs(example) == sp.Rational(1, 6), "shear passes a nonarithmetic triple")


def main() -> int:
    for check in (check_scalar_means, check_reciprocal_derivatives, check_matrix_coefficients,
                  check_mixed_coordinates, check_shear_control):
        check()
        print(f"PASS {check.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
