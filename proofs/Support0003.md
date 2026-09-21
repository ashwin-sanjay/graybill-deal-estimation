# Checked raw-to-projective variable-risk transfer

The raw both-individual-means consequence uses the following variable-envelope reduction. At every native `m,n >= 2`, a
raw Borel rule below a nonnegative, reflection-invariant physical envelope
with the positive-affine squared-error character and one finite oracle cap
yields one measurable projective coefficient in `[0,1]` below the same envelope.

For `min(sigmaX^2/m, sigmaY^2/n)`, the checked theorem gives

```
integral (g(z)-t)^2 d(interiorLaw m n t)
  <= (min(t,1-t) / max(t,1-t)) * t * (1-t).
```

The exact anchor is
`GD.N0100.N0347.d024059`
in [Supporting evidence](../GD/Module1557.lean).
This supplies the reduction discussed in the earlier
[variable-cap review](Support0002.md). The actual packet
integrals and realization of the window-bound hypotheses are separate: this transfer does not
certify those analytic estimates. The native (3,3) obstruction retains its
paper-proof evidence for those analytic estimates.
