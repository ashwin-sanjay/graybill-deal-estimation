import GD.Module0340






set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators Polynomial

namespace GD.N0106.N0428.N0766.N1692.N1761
noncomputable section

open Polynomial _root_.GD.N0232.N0720.N1254


def d005069 (gamma : ℝ) : Fin 3 → ℝ[X] :=
  ![_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 2, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3]

def d005070 (gamma : ℝ) : Submodule ℝ ℝ[X] :=
  Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005069 gamma))

theorem d005071 (gamma : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0 = (1 / (2 * gamma)) • (X : ℝ[X]) := by
  change C (1 / (2 * gamma)) * X = _
  rw [Polynomial.smul_eq_C_mul]

theorem d005072 (gamma : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 2 =
      (-4 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma) • (X : ℝ[X]) +
        (2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) •
          (X ^ 3 : ℝ[X]) := by
  change C (-4 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma) * X +
    C (2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) *
      X ^ 3 = _
  simp only [Polynomial.smul_eq_C_mul]

theorem d005073 (gamma : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3 =
      (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 2)) • (X : ℝ[X]) +
        (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 4)) • (X ^ 3 : ℝ[X]) := by
  change C (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 2)) * X +
    C (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 4)) * X ^ 3 = _
  simp only [Polynomial.smul_eq_C_mul]


theorem d005074 {gamma : ℝ} (hgamma : 0 < gamma) :
    (2 * gamma) • _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0 = (X : ℝ[X]) := by
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005071, smul_smul]
  have hcancel : (2 * gamma) * (1 / (2 * gamma)) = 1 := by
    field_simp [hgamma.ne']
  rw [hcancel, one_smul]


theorem d005075 {gamma : ℝ}
    (hgamma : 0 < gamma) :
    (8 * gamma ^ 4 / _root_.GD.N0232.N0720.N1254.d002513 gamma gamma) • _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3 +
      gamma ^ 2 • (X : ℝ[X]) = (X ^ 3 : ℝ[X]) := by
  have hr : 0 < _root_.GD.N0232.N0720.N1254.d002513 gamma gamma := by
    unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
    positivity
  have hlinear :
      (8 * gamma ^ 4 / _root_.GD.N0232.N0720.N1254.d002513 gamma gamma) *
        (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 2)) = -(gamma ^ 2) := by
    field_simp [hgamma.ne', hr.ne'] <;> ring
  have hcubic :
      (8 * gamma ^ 4 / _root_.GD.N0232.N0720.N1254.d002513 gamma gamma) *
        (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 4)) = 1 := by
    field_simp [hgamma.ne', hr.ne']
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005073, smul_add, smul_smul, smul_smul,
    hlinear, hcubic, one_smul]
  simp only [neg_smul]
  abel


theorem d005076 (gamma : ℝ) (j : Fin 3) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005069 gamma j ∈
      Submodule.span ℝ ({(X : ℝ[X]), (X ^ 3 : ℝ[X])} : Set ℝ[X]) := by
  let S := Submodule.span ℝ ({(X : ℝ[X]), (X ^ 3 : ℝ[X])} : Set ℝ[X])
  have hX : (X : ℝ[X]) ∈ S := Submodule.subset_span (by simp)
  have hX3 : (X ^ 3 : ℝ[X]) ∈ S := Submodule.subset_span (by simp)
  fin_cases j
  · change _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0 ∈ S
    rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005071]
    exact S.smul_mem _ hX
  · change _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 2 ∈ S
    rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005072]
    exact S.add_mem (S.smul_mem _ hX) (S.smul_mem _ hX3)
  · change _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3 ∈ S
    rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005073]
    exact S.add_mem (S.smul_mem _ hX) (S.smul_mem _ hX3)


theorem d005077 {gamma : ℝ} (hgamma : 0 < gamma) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma =
      Submodule.span ℝ ({(X : ℝ[X]), (X ^ 3 : ℝ[X])} : Set ℝ[X]) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨j, rfl⟩
    exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005076 gamma j
  · have hzero : _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0 ∈ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma :=
      Submodule.subset_span ⟨(0 : Fin 3), rfl⟩
    have hthree : _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3 ∈ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma :=
      Submodule.subset_span ⟨(2 : Fin 3), rfl⟩
    have hX : (X : ℝ[X]) ∈ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma := by
      rw [← _root_.GD.N0106.N0428.N0766.N1692.N1761.d005074 hgamma]
      exact (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma).smul_mem _ hzero
    have hX3 : (X ^ 3 : ℝ[X]) ∈ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma := by
      rw [← _root_.GD.N0106.N0428.N0766.N1692.N1761.d005075 hgamma]
      exact (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma).add_mem
        ((_root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma).smul_mem _ hthree) ((_root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma).smul_mem _ hX)
    apply Submodule.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hX
    · have hp' : p = (X ^ 3 : ℝ[X]) := Set.mem_singleton_iff.mp hp
      rw [hp']
      exact hX3


theorem d005078 {gamma : ℝ} (hgamma : 0 < gamma) :
    Module.finrank ℝ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005070 gamma) = 2 := by
  have hli : LinearIndependent ℝ (![X, X ^ 3] : Fin 2 → ℝ[X]) := by
    apply LinearIndependent.pair_iff.mpr
    intro a b hab
    constructor
    · have h := congrArg (fun p : ℝ[X] => p.coeff 1) hab
      simpa [Polynomial.coeff_X] using h
    · have h := congrArg (fun p : ℝ[X] => p.coeff 3) hab
      simpa [Polynomial.coeff_X] using h
  have hrange : Set.range (![X, X ^ 3] : Fin 2 → ℝ[X]) =
      ({(X : ℝ[X]), (X ^ 3 : ℝ[X])} : Set ℝ[X]) := by
    ext p
    simp [Fin.exists_fin_two, eq_comm, or_comm]
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005077 hgamma, ← hrange]
  simpa only [Fintype.card_fin] using finrank_span_eq_card hli


theorem d005079 {gamma : ℝ} (hgamma : 0 < gamma)
    (j : Fin 4) (hj : j ≠ 1) : _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j ≠ 0 := by
  have hr : 0 < _root_.GD.N0232.N0720.N1254.d002513 gamma gamma := by
    unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
    positivity
  fin_cases j
  · have hc : 0 < (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0).coeff 1 := by
      change 0 < (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 1
      rw [Polynomial.coeff_C_mul_X, if_pos rfl]
      exact div_pos (by norm_num) (mul_pos (by norm_num) hgamma)
    intro hz
    change _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0 = 0 at hz
    rw [hz, Polynomial.coeff_zero] at hc
    exact (lt_irrefl (0 : ℝ)) hc
  · exact (hj rfl).elim
  · have hc : 0 < (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 2).coeff 3 := by
      change 0 < (C (-4 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma) * X +
        C (2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) *
          X ^ 3 : ℝ[X]).coeff 3
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C_mul_X_pow]
      norm_num <;> positivity
    intro hz
    change _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 2 = 0 at hz
    rw [hz, Polynomial.coeff_zero] at hc
    exact (lt_irrefl (0 : ℝ)) hc
  · have hc : 0 < (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3).coeff 3 := by
      change 0 < (C (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 2)) * X +
        C (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 3
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C_mul_X_pow]
      norm_num <;> positivity
    intro hz
    change _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3 = 0 at hz
    rw [hz, Polynomial.coeff_zero] at hc
    exact (lt_irrefl (0 : ℝ)) hc


theorem d005080 {gamma : ℝ} (hgamma : 0 < gamma)
    (j : Fin 4) :
    (∀ d : ℝ, (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).eval (-d) =
      (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).eval d) ↔ j = 1 := by
  constructor
  · intro heven
    by_contra hj
    apply _root_.GD.N0106.N0428.N0766.N1692.N1761.d005079 hgamma j hj
    apply Polynomial.zero_of_eval_zero
    intro d
    have hodd := _root_.GD.N0106.N0428.N0766.N1692.N1761.d005068 gamma d j hj
    have he := heven d
    linarith
  · rintro rfl
    exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005067 gamma


def d005081 (gamma : ℝ) (weights : Fin 4 → ℝ) : ℝ[X] :=
  ∑ j, weights j • _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j

theorem d005082 (gamma : ℝ) (weights : Fin 4 → ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005081 gamma weights ∈ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma := by
  apply Submodule.sum_mem
  intro j _
  exact (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma).smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)


theorem d005083 (gamma : ℝ) (weights : Fin 4 → ℝ) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005081 gamma weights).coeff 0 = weights 1 := by
  have hc (j : Fin 4) : _root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma (0 : Fin 4) j =
      (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).coeff 0 :=
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005032 gamma (0 : Fin 4) j
  simp only [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005081, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul]
  simp_rw [← hc]
  simp only [Fin.sum_univ_succ]
  change weights 0 * 0 + (weights 1 * 1 + (weights 2 * 0 + (weights 3 * 0 + 0))) =
    weights 1
  ring


theorem d005084 (gamma : ℝ) (weights : Fin 4 → ℝ) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005081 gamma weights).coeff 2 =
      (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * weights 1 := by
  have h := _root_.GD.N0106.N0428.N0766.N1692.N1761.d005064
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005082 gamma weights)
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005083] at h
  exact h



theorem d005085 {gamma : ℝ}
    (hgamma : 0 < gamma) (weights : Fin 4 → ℝ)
    (hquadratic : (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005081 gamma weights).coeff 2 = 0) :
    weights 1 = 0 ∧ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005081 gamma weights).coeff 0 = 0 := by
  have hr : 0 < _root_.GD.N0232.N0720.N1254.d002513 gamma gamma := by
    unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
    positivity
  have hfactor : -_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hr.ne') (pow_ne_zero _ hgamma.ne')
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005084] at hquadratic
  have hweight : weights 1 = 0 := (mul_eq_zero.mp hquadratic).resolve_left hfactor
  exact ⟨hweight, (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005083 gamma weights).trans hweight⟩

end
end GD.N0106.N0428.N0766.N1692.N1761

#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005074
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005075
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005077
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005078
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005080
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005083
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005084
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005085
