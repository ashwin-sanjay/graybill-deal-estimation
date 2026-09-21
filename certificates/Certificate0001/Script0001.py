#!/usr/bin/env python3
"""Deterministic exact audit for the eight-tent six-jet/eight-node algebra.

This script is a reproducibility aid, not proof authority.  It checks only
polynomial/rational identities.  The analytic tent-smearing and energy
arguments live in the paper and their finite compilers belong in Lean.
"""

from sympy import Matrix, Poly, expand, factor, simplify, symbols


def main() -> None:
    r, nu, p = symbols("r nu p", nonzero=True)
    Delta, d = symbols("Delta d")
    c = p / nu
    a = (d + Delta) / nu
    hcoef = (p - Delta * d - d**2) / (2 * nu**2)
    x = d / c
    z = hcoef / c

    jets = [
        a,
        1 - r * a * x,
        -2 * r * x + r * (r + 1) * a * x**2,
        3 * r * (r + 1) * x**2
        - r * (r + 1) * (r + 2) * a * x**3,
        -r * a * z,
        r * z * ((r + 1) * a * x - 1),
    ]
    coeffs = [
        Delta * nu * r * (r + 1) / p,
        (Delta**2 * r * (r + 1) - p * (r**2 + r + 1))
        / (p * (r - 1)),
        -2 * Delta * (r + 1) / (nu * (r - 1)),
        p / (nu**2 * (r - 1)),
        2 * Delta * nu**2 * r * (r + 1) / (p * (r - 1)),
        -2 * nu * (r + 2) / (r - 1),
    ]
    six_jet_residual = sum(v * jet for v, jet in zip(coeffs, jets)) - 1
    assert factor(six_jet_residual) == 0
    assert factor(six_jet_residual.subs(Delta, 0)) == 0

    hs, eta = symbols("hs eta", nonzero=True)
    v00, v10, v20, v30, v01, v11 = symbols(
        "v00 v10 v20 v30 v01 v11"
    )
    fm2, fm, f0, fp, fp2, gm, g0, gp = symbols(
        "fm2 fm f0 fp fp2 gm g0 gp"
    )
    differences = [
        f0,
        (fp - fm) / (2 * hs),
        (fp - 2 * f0 + fm) / hs**2,
        (fp2 - 2 * fp + 2 * fm - fm2) / (2 * hs**3),
        (g0 - f0) / eta,
        ((gp - gm) - (fp - fm)) / (2 * hs * eta),
    ]
    finite_action = -sum(
        v * value
        for v, value in zip(
            [v00, v10, v20, v30, v01, v11], differences
        )
    )
    weights = [
        v30 / (2 * hs**3),
        v10 / (2 * hs) - v20 / hs**2 - v30 / hs**3
        - v11 / (2 * hs * eta),
        -v00 + 2 * v20 / hs**2 + v01 / eta,
        -v10 / (2 * hs) - v20 / hs**2 + v30 / hs**3
        + v11 / (2 * hs * eta),
        -v30 / (2 * hs**3),
        v11 / (2 * hs * eta),
        -v01 / eta,
        -v11 / (2 * hs * eta),
    ]
    node_values = [fm2, fm, f0, fp, fp2, gm, g0, gp]
    assert simplify(finite_action - sum(
        w * value for w, value in zip(weights, node_values)
    )) == 0

    # Shape exchange: Delta changes sign and local s is reflected.  The
    # transformed weight at reflected s must be the negative original weight.
    parity = {
        v00: -v00,
        v10: v10,
        v20: -v20,
        v30: v30,
        v01: -v01,
        v11: v11,
    }
    swapped = [simplify(w.subs(parity, simultaneous=True)) for w in weights]
    reflected_index = [4, 3, 2, 1, 0, 7, 6, 5]
    for i, j in enumerate(reflected_index):
        assert simplify(swapped[j] + weights[i]) == 0

    # At alpha=beta=gamma, the old 00/10/20/01 family cannot hit 1.
    gamma = symbols("gamma", nonzero=True)
    a_bal = d / (2 * gamma)
    x_bal = 2 * d / gamma
    z_bal = (gamma**2 - d**2) / (4 * gamma**3)
    old_jets = [
        a_bal,
        1 - r * a_bal * x_bal,
        -2 * r * x_bal + r * (r + 1) * a_bal * x_bal**2,
        -r * a_bal * z_bal,
    ]
    matrix = Matrix([
        [Poly(expand(jet), d).coeff_monomial(d**degree)
         for jet in old_jets]
        for degree in range(4)
    ])
    target = Matrix([1, 0, 0, 0])
    assert matrix.rank() == 3
    assert matrix.row_join(target).rank() == 4

    print("PASS six-jet identity")
    print("PASS eight-node expansion")
    print("PASS swap parity")
    print("PASS balanced four-jet rank obstruction (3 < 4)")


if __name__ == "__main__":
    main()
