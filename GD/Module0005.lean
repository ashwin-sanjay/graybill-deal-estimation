import Mathlib.Analysis.Normed.Module.Basic










namespace GD
namespace N0230
namespace N0557

variable {G Theta D H : Type*}
variable [Group G] [MulAction G Theta] [MulAction G D]


def d000040
    (risk : Theta → D → ℝ) (weight : G → ℝ) : Prop :=
  ∀ (g : G) (theta : Theta) (d : D),
    risk (g • theta) (g • d) = weight g * risk theta d


def d000041
    (risk : Theta → D → ℝ) (theta : Theta) (p : D) (g : G) : ℝ :=
  risk theta (g • p) - risk theta p


def d000042
    (risk : Theta → D → ℝ) (theta : Theta) (p : D) (g : G) : ℝ :=
  risk theta (g • p) + risk (g • theta) p -
    risk theta p - risk (g • theta) (g • p)


theorem d000043
    (risk : Theta → D → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (theta : Theta) (p : D) (g : G) :
    _root_.GD.N0230.N0557.d000042 risk theta p g =
      _root_.GD.N0230.N0557.d000041 risk theta p g +
        weight g * _root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ := by
  have hforward := hRisk g theta p
  have hback := hRisk g theta (g⁻¹ • p)
  simp only [smul_inv_smul] at hback
  unfold _root_.GD.N0230.N0557.d000042 _root_.GD.N0230.N0557.d000041
  rw [hforward, hback]
  ring


theorem d000044
    (risk : Theta → D → ℝ) (theta : Theta) (p : D)
    (hmin : ∀ g : G, risk theta p ≤ risk theta (g • p))
    (g : G) :
    0 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g := by
  unfold _root_.GD.N0230.N0557.d000041
  linarith [hmin g]


theorem d000045
    (risk : Theta → D → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (p : D)
    (hmin : ∀ g : G, risk theta p ≤ risk theta (g • p))
    (g : G) :
    0 ≤ _root_.GD.N0230.N0557.d000042 risk theta p g := by
  rw [_root_.GD.N0230.N0557.d000043 risk weight hRisk theta p g]
  exact add_nonneg (_root_.GD.N0230.N0557.d000044 risk theta p hmin g)
    (mul_nonneg (le_of_lt (hweight g))
      (_root_.GD.N0230.N0557.d000044 risk theta p hmin g⁻¹))

section FaithfulTax

variable [NormedAddCommGroup H]


theorem d000046
    (risk : Theta → D → ℝ) (theta : Theta) (p : D)
    (J : D → H) (hJ : Function.Injective J)
    (htax : ∀ g : G,
      ‖J (g • p) - J p‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g)
    (g : G) :
    _root_.GD.N0230.N0557.d000041 risk theta p g = 0 ↔ g • p = p := by
  constructor
  · intro hzero
    have hsquare : ‖J (g • p) - J p‖ ^ 2 ≤ 0 := by
      simpa [hzero] using htax g
    have hnorm : ‖J (g • p) - J p‖ = 0 := by
      nlinarith [norm_nonneg (J (g • p) - J p)]
    exact hJ (sub_eq_zero.mp (norm_eq_zero.mp hnorm))
  · intro hfixed
    simp [_root_.GD.N0230.N0557.d000041, hfixed]


theorem d000047
    (risk : Theta → D → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (p : D)
    (hmin : ∀ g : G, risk theta p ≤ risk theta (g • p))
    (J : D → H) (hJ : Function.Injective J)
    (htax : ∀ g : G,
      ‖J (g • p) - J p‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g)
    (g : G) :
    _root_.GD.N0230.N0557.d000042 risk theta p g = 0 ↔ g • p = p := by
  constructor
  · intro hzero
    have hid := _root_.GD.N0230.N0557.d000043
      risk weight hRisk theta p g
    have hg : 0 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g :=
      _root_.GD.N0230.N0557.d000044 risk theta p hmin g
    have hginv : 0 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ :=
      _root_.GD.N0230.N0557.d000044 risk theta p hmin g⁻¹
    have hw : 0 < weight g := hweight g
    have hreg : _root_.GD.N0230.N0557.d000041 risk theta p g = 0 := by
      nlinarith [mul_nonneg (le_of_lt hw) hginv]
    exact (_root_.GD.N0230.N0557.d000046 risk theta p J hJ htax g).mp hreg
  · intro hfixed
    unfold _root_.GD.N0230.N0557.d000042
    rw [hfixed]
    ring


theorem d000048
    (risk : Theta → D → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (p : D)
    (hmin : ∀ g : G, risk theta p ≤ risk theta (g • p))
    (J : D → H) (hJ : Function.Injective J)
    (htax : ∀ g : G,
      ‖J (g • p) - J p‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g)
    (g : G) (hnot : g • p ≠ p) :
    0 < _root_.GD.N0230.N0557.d000042 risk theta p g := by
  have hnonneg := _root_.GD.N0230.N0557.d000045
    risk weight hRisk hweight theta p hmin g
  exact lt_of_le_of_ne hnonneg (fun h ↦ hnot
    ((_root_.GD.N0230.N0557.d000047
      risk weight hRisk hweight theta p hmin J hJ htax g).mp h.symm))


theorem d000049
    (risk : Theta → D → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (p : D)
    (hmin : ∀ g : G, risk theta p ≤ risk theta (g • p))
    (J : D → H) (hJ : Function.Injective J)
    (htax : ∀ g : G,
      ‖J (g • p) - J p‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g) :
    (∀ g : G, g • p = p) ↔
      ∀ g : G, _root_.GD.N0230.N0557.d000042 risk theta p g = 0 := by
  constructor
  · intro hfixed g
    exact (_root_.GD.N0230.N0557.d000047
      risk weight hRisk hweight theta p hmin J hJ htax g).mpr (hfixed g)
  · intro hzero g
    exact (_root_.GD.N0230.N0557.d000047
      risk weight hRisk hweight theta p hmin J hJ htax g).mp (hzero g)

end FaithfulTax


theorem d000050
    (risk : Theta → D → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hinv : ∀ g, weight g * weight g⁻¹ = 1)
    (theta : Theta) (p : D) (g : G) :
    _root_.GD.N0230.N0557.d000042 risk theta p g =
      weight g * _root_.GD.N0230.N0557.d000042 risk theta p g⁻¹ := by
  rw [_root_.GD.N0230.N0557.d000043 risk weight hRisk theta p g,
      _root_.GD.N0230.N0557.d000043 risk weight hRisk theta p g⁻¹]
  simp only [inv_inv]
  calc
    _root_.GD.N0230.N0557.d000041 risk theta p g +
          weight g * _root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ =
        weight g * _root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ +
          (weight g * weight g⁻¹) * _root_.GD.N0230.N0557.d000041 risk theta p g := by
            rw [hinv g]
            ring
    _ = weight g *
          (_root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ +
            weight g⁻¹ * _root_.GD.N0230.N0557.d000041 risk theta p g) := by ring

end N0557
end N0230
end GD

#print axioms _root_.GD.N0230.N0557.d000043
#print axioms _root_.GD.N0230.N0557.d000047
#print axioms _root_.GD.N0230.N0557.d000049
#print axioms _root_.GD.N0230.N0557.d000050
