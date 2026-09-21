import GD.Module0339






set_option autoImplicit false
set_option warningAsError true

open scoped Polynomial

namespace GD.N0106.N0428.N0766.N1692.N1761
noncomputable section

open Polynomial _root_.GD.N0232.N0720.N1254

def d005055 (gamma : ℝ) : Submodule ℝ ℝ[X] :=
  Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma))

def d005056 (gamma : ℝ) : Submodule ℝ ℝ[X] :=
  Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005035 gamma))

theorem d005057 (gamma : ℝ) (j : Fin 4) :
    Polynomial.ofFn 4 ((_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).col j) = _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j := by
  ext n
  by_cases hn : n < 4
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hn]
    exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005032 gamma ⟨n, hn⟩ j
  · have hn' : 4 ≤ n := Nat.le_of_not_gt hn
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hn',
      _root_.GD.N0106.N0428.N0766.N1692.N1761.d005033 gamma j hn']

theorem d005058 (gamma : ℝ) (j : Fin 5)
    {n : ℕ} (hn : 4 ≤ n) : (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005035 gamma j).coeff n = 0 := by
  fin_cases j
  · exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005033 gamma 0 hn
  · exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005033 gamma 1 hn
  · exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005033 gamma 2 hn
  · exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005033 gamma 3 hn
  · change (1 : ℝ[X]).coeff n = 0
    have hn0 : n ≠ 0 := by omega
    simp [Polynomial.coeff_one, hn0]

theorem d005059 (gamma : ℝ) (j : Fin 5) :
    Polynomial.ofFn 4 ((_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).col j) = _root_.GD.N0106.N0428.N0766.N1692.N1761.d005035 gamma j := by
  ext n
  by_cases hn : n < 4
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hn]
    exact _root_.GD.N0106.N0428.N0766.N1692.N1761.d005037 gamma ⟨n, hn⟩ j
  · have hn' : 4 ≤ n := Nat.le_of_not_gt hn
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hn',
      _root_.GD.N0106.N0428.N0766.N1692.N1761.d005058 gamma j hn']

theorem d005060 (gamma : ℝ) :
    (Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).col)).map
        (Polynomial.ofFn (R := ℝ) 4) = _root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma := by
  rw [Submodule.map_span, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005055]
  congr 1
  ext p
  constructor
  · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005057 gamma j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).col j, ⟨j, rfl⟩,
      _root_.GD.N0106.N0428.N0766.N1692.N1761.d005057 gamma j⟩

theorem d005061 (gamma : ℝ) :
    (Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).col)).map
        (Polynomial.ofFn (R := ℝ) 4) = _root_.GD.N0106.N0428.N0766.N1692.N1761.d005056 gamma := by
  rw [Submodule.map_span, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005056]
  congr 1
  ext p
  constructor
  · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005059 gamma j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).col j, ⟨j, rfl⟩,
      _root_.GD.N0106.N0428.N0766.N1692.N1761.d005059 gamma j⟩


theorem d005062 {gamma : ℝ} (hgamma : 0 < gamma) :
    Module.finrank ℝ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma) = 3 := by
  calc
    Module.finrank ℝ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma) =
        Module.finrank ℝ (Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).col)) := by
      rw [← _root_.GD.N0106.N0428.N0766.N1692.N1761.d005060 gamma]
      exact (Submodule.equivMapOfInjective (Polynomial.ofFn (R := ℝ) 4)
        (Polynomial.injective_ofFn 4) _).finrank_eq.symm
    _ = (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).rank :=
      (Matrix.rank_eq_finrank_span_cols _).symm
    _ = 3 := _root_.GD.N0106.N0428.N0766.N1692.N1761.d005048 hgamma


theorem d005063 {gamma : ℝ} (hgamma : 0 < gamma) :
    Module.finrank ℝ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005056 gamma) = 4 := by
  calc
    Module.finrank ℝ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005056 gamma) =
        Module.finrank ℝ (Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).col)) := by
      rw [← _root_.GD.N0106.N0428.N0766.N1692.N1761.d005061 gamma]
      exact (Submodule.equivMapOfInjective (Polynomial.ofFn (R := ℝ) 4)
        (Polynomial.injective_ofFn 4) _).finrank_eq.symm
    _ = (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).rank :=
      (Matrix.rank_eq_finrank_span_cols _).symm
    _ = 4 := _root_.GD.N0106.N0428.N0766.N1692.N1761.d005053 hgamma



theorem d005064 {gamma : ℝ} {p : ℝ[X]}
    (hp : p ∈ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma) :
    p.coeff 2 = (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * p.coeff 0 := by
  change p ∈ Submodule.span ℝ (Set.range (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma)) at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨j, rfl⟩ := hp
    have h2 : _root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma (2 : Fin 4) j =
        (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).coeff 2 :=
      _root_.GD.N0106.N0428.N0766.N1692.N1761.d005032 gamma (2 : Fin 4) j
    have h0 : _root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma (0 : Fin 4) j =
        (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).coeff 0 :=
      _root_.GD.N0106.N0428.N0766.N1692.N1761.d005032 gamma (0 : Fin 4) j
    rw [← h2, ← h0]
    fin_cases j
    · change (0 : ℝ) = (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * 0
      ring
    · change (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2 : ℝ) =
        (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * 1
      ring
    · change (0 : ℝ) = (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * 0
      ring
    · change (0 : ℝ) = (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * 0
      ring
  | zero => simp
  | add p q hp hq ihp ihq =>
    simp only [Polynomial.coeff_add, ihp, ihq]
    ring
  | smul a p hp ih =>
    simp only [Polynomial.coeff_smul, smul_eq_mul, ih]
    ring



theorem d005065 {gamma : ℝ} (hgamma : 0 < gamma)
    {p : ℝ[X]} (hp : p ∈ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma) (h2 : p.coeff 2 = 0) : p.coeff 0 = 0 := by
  have hr : 0 < _root_.GD.N0232.N0720.N1254.d002513 gamma gamma := by
    unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
    linarith
  have hfactor : (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2 : ℝ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hr.ne') (pow_ne_zero _ hgamma.ne')
  exact (mul_eq_zero.mp ((_root_.GD.N0106.N0428.N0766.N1692.N1761.d005064 hp).symm.trans h2)).resolve_left hfactor

theorem d005066 {gamma : ℝ} (hgamma : 0 < gamma) :
    (1 : ℝ[X]) ∉ _root_.GD.N0106.N0428.N0766.N1692.N1761.d005055 gamma := by
  intro h1
  have h := _root_.GD.N0106.N0428.N0766.N1692.N1761.d005065 hgamma h1 (by simp [Polynomial.coeff_one])
  simpa using h


theorem d005067 (gamma d : ℝ) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 1).eval (-d) = (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 1).eval d := by
  change (1 - C (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * X ^ 2 : ℝ[X]).eval (-d) =
    (1 - C (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) * X ^ 2 : ℝ[X]).eval d
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring


theorem d005068 (gamma d : ℝ) (j : Fin 4) (hj : j ≠ 1) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).eval (-d) = -(_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).eval d := by
  fin_cases j
  · change (C (1 / (2 * gamma)) * X : ℝ[X]).eval (-d) =
      -(C (1 / (2 * gamma)) * X : ℝ[X]).eval d
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  · exact (hj rfl).elim
  · change (C (-4 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma) * X +
        C (2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) *
          X ^ 3 : ℝ[X]).eval (-d) =
      -(C (-4 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma) * X +
        C (2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) *
          X ^ 3 : ℝ[X]).eval d
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  · change (C (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 2)) * X +
        C (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).eval (-d) =
      -(C (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 2)) * X +
        C (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).eval d
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring

end
end GD.N0106.N0428.N0766.N1692.N1761

#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005062
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005063
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005066
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005067
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005068
