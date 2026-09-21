import GD.Module1034















































open Filter MeasureTheory Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1039

noncomputable section





def d016521 (A c : ℝ) : ℝ := 1 + c * (A - 1)



def d016522 (a b M A c : ℝ) : ℝ :=
  (a * M * (c - 1) - b * A) / (_root_.GD.N0232.N0720.N1039.d016521 A c * A)


def d016523 (a b mu c : ℝ) : ℝ := a * mu * (c - 1) - b

theorem d016524 {A c : ℝ} (hA : 1 ≤ A) (hc : 0 < c) :
    0 < _root_.GD.N0232.N0720.N1039.d016521 A c := by
  unfold _root_.GD.N0232.N0720.N1039.d016521
  nlinarith

theorem d016525 {A c : ℝ} (hA : 1 ≤ A) (hc : 0 < c) :
    1 ≤ _root_.GD.N0232.N0720.N1039.d016521 A c := by
  unfold _root_.GD.N0232.N0720.N1039.d016521
  nlinarith




theorem d016526 {a b M A c : ℝ}
    (hA : A ≠ 0) (ht : _root_.GD.N0232.N0720.N1039.d016521 A c ≠ 0) :
    _root_.GD.N0232.N0720.N1039.d016521 A c * _root_.GD.N0232.N0720.N1039.d016522 a b M A c ^ 2 =
      _root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c ^ 2 / _root_.GD.N0232.N0720.N1039.d016521 A c := by
  unfold _root_.GD.N0232.N0720.N1039.d016522 _root_.GD.N0232.N0720.N1039.d016523
  field_simp


theorem d016527 {a b M A c : ℝ}
    (hA : 1 ≤ A) (hc : 0 < c) :
    0 ≤ _root_.GD.N0232.N0720.N1039.d016521 A c * _root_.GD.N0232.N0720.N1039.d016522 a b M A c ^ 2 :=
  mul_nonneg (_root_.GD.N0232.N0720.N1039.d016524 hA hc).le (sq_nonneg _)




theorem d016528 {a b M A c K : ℝ}
    (hA : 1 ≤ A) (hc : 0 < c)
    (hK : |_root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c| ≤ K) :
    _root_.GD.N0232.N0720.N1039.d016521 A c * _root_.GD.N0232.N0720.N1039.d016522 a b M A c ^ 2 ≤
      K ^ 2 / _root_.GD.N0232.N0720.N1039.d016521 A c := by
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have ht := _root_.GD.N0232.N0720.N1039.d016524 hA hc
  have hnum : _root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c ^ 2 ≤ K ^ 2 := by
    have habs := sq_abs (_root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c)
    have hpos := abs_nonneg (_root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c)
    nlinarith
  rw [_root_.GD.N0232.N0720.N1039.d016526 hApos.ne' ht.ne']
  have hinv : (0 : ℝ) ≤ (_root_.GD.N0232.N0720.N1039.d016521 A c)⁻¹ := (inv_pos.mpr ht).le
  calc _root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c ^ 2 / _root_.GD.N0232.N0720.N1039.d016521 A c
      = _root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c ^ 2 * (_root_.GD.N0232.N0720.N1039.d016521 A c)⁻¹ :=
        div_eq_mul_inv _ _
    _ ≤ K ^ 2 * (_root_.GD.N0232.N0720.N1039.d016521 A c)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum hinv
    _ = K ^ 2 / _root_.GD.N0232.N0720.N1039.d016521 A c := (div_eq_mul_inv _ _).symm

theorem d016529 {a b M A c K : ℝ}
    (hA : 1 ≤ A) (hc : 0 < c)
    (hK : |_root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c| ≤ K) :
    _root_.GD.N0232.N0720.N1039.d016521 A c * _root_.GD.N0232.N0720.N1039.d016522 a b M A c ^ 2 ≤ K ^ 2 := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) hK
  have h1 := _root_.GD.N0232.N0720.N1039.d016528 hA hc hK
  have ht := _root_.GD.N0232.N0720.N1039.d016525 hA hc
  have htpos := _root_.GD.N0232.N0720.N1039.d016524 hA hc
  have h2 : K ^ 2 / _root_.GD.N0232.N0720.N1039.d016521 A c ≤ K ^ 2 := by
    rw [div_le_iff₀ htpos]
    nlinarith [sq_nonneg K]
  linarith



theorem d016530 {c : ℝ} (hc : 0 < c) {A : ℕ → ℝ}
    (hA : Tendsto A atTop atTop) :
    Tendsto (fun j => _root_.GD.N0232.N0720.N1039.d016521 (A j) c) atTop atTop := by
  unfold _root_.GD.N0232.N0720.N1039.d016521
  have h1 : Tendsto (fun j => A j - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) hA
  have h2 : Tendsto (fun j => c * (A j - 1)) atTop atTop := h1.const_mul_atTop hc
  exact tendsto_atTop_add_const_left atTop (1 : ℝ) h2

theorem d016531 {c K : ℝ} (hc : 0 < c) {A : ℕ → ℝ}
    (hA : Tendsto A atTop atTop) :
    Tendsto (fun j => K ^ 2 / _root_.GD.N0232.N0720.N1039.d016521 (A j) c) atTop (𝓝 0) := by
  have h := _root_.GD.N0232.N0720.N1039.d016530 hc hA
  have hinv : Tendsto (fun j => (_root_.GD.N0232.N0720.N1039.d016521 (A j) c)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h
  have := hinv.const_mul (K ^ 2)
  simpa [div_eq_mul_inv] using this




theorem d016532 {a b c K : ℝ} (hc : 0 < c)
    {A M : ℕ → ℝ} (hA1 : ∀ j, 1 ≤ A j)
    (hK : ∀ j, |_root_.GD.N0232.N0720.N1039.d016523 a b (M j / A j) c| ≤ K)
    (hA : Tendsto A atTop atTop) :
    Tendsto (fun j => _root_.GD.N0232.N0720.N1039.d016521 (A j) c * _root_.GD.N0232.N0720.N1039.d016522 a b (M j) (A j) c ^ 2)
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun j => _root_.GD.N0232.N0720.N1039.d016527 (hA1 j) hc)
    (fun j => _root_.GD.N0232.N0720.N1039.d016528 (hA1 j) hc (hK j))
  exact _root_.GD.N0232.N0720.N1039.d016531 hc hA






theorem d016533 {mu c₀ c₁ : ℝ}
    (h₀ : _root_.GD.N0232.N0720.N1039.d016523 2 0 mu c₀ = 0)
    (h₁ : _root_.GD.N0232.N0720.N1039.d016523 3 1 mu c₁ = 0) :
    mu ≠ 0 ∧ c₀ = 1 := by
  unfold _root_.GD.N0232.N0720.N1039.d016523 at h₀ h₁
  have hmu : mu ≠ 0 := by
    intro h
    rw [h] at h₁
    norm_num at h₁
  refine ⟨hmu, ?_⟩
  have hzero : 2 * mu * (c₀ - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · norm_num at h'
    · exact absurd h' hmu
  · linarith



theorem d016534 {mu c₀ c₁ : ℝ} (hc₀ : c₀ ≠ 1) :
    ¬ (_root_.GD.N0232.N0720.N1039.d016523 2 0 mu c₀ = 0 ∧ _root_.GD.N0232.N0720.N1039.d016523 3 1 mu c₁ = 0) := by
  rintro ⟨h₀, h₁⟩
  exact hc₀ (_root_.GD.N0232.N0720.N1039.d016533 h₀ h₁).2



theorem d016535 {mu c : ℝ} :
    _root_.GD.N0232.N0720.N1039.d016523 2 0 mu c = 0 ↔ mu = 0 ∨ c = 1 := by
  unfold _root_.GD.N0232.N0720.N1039.d016523
  constructor
  · intro h
    have hzero : 2 * mu * (c - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact Or.inl h''
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> rw [h] <;> ring



theorem d016536 {c : ℝ} :
    _root_.GD.N0232.N0720.N1039.d016523 3 1 0 c ≠ 0 := by
  unfold _root_.GD.N0232.N0720.N1039.d016523
  norm_num












theorem d016537 {mu c₀ c₁ ε : ℝ}
    (hε : |_root_.GD.N0232.N0720.N1039.d016523 3 1 mu c₁| ≤ ε) :
    2 * (1 - ε) * |c₀ - 1| ≤ 3 * |_root_.GD.N0232.N0720.N1039.d016523 2 0 mu c₀| * |c₁ - 1| := by
  unfold _root_.GD.N0232.N0720.N1039.d016523 at hε ⊢
  rw [sub_zero]
  have hN0 : |2 * mu * (c₀ - 1)| = 2 * |mu| * |c₀ - 1| := by
    rw [abs_mul, abs_mul]
    norm_num
  have hX : |3 * mu * (c₁ - 1)| = 3 * |mu| * |c₁ - 1| := by
    rw [abs_mul, abs_mul]
    norm_num
  have htri : (1 : ℝ) - |3 * mu * (c₁ - 1)| ≤ |3 * mu * (c₁ - 1) - 1| := by
    have h := abs_sub_abs_le_abs_sub (1 : ℝ) (3 * mu * (c₁ - 1))
    rw [abs_one, abs_sub_comm] at h
    exact h
  have hkey : 1 - ε ≤ 3 * |mu| * |c₁ - 1| := by
    rw [← hX]
    linarith
  rw [hN0]
  have hmul := mul_le_mul_of_nonneg_left hkey
    (by positivity : (0 : ℝ) ≤ 2 * |c₀ - 1|)
  nlinarith [hmul, abs_nonneg mu, abs_nonneg (c₀ - 1), abs_nonneg (c₁ - 1)]









theorem d016538
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {a b K : ℝ} {c : Ω → ℝ} {A M : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hc : ∀ ω, 0 < c ω)
    (hA1 : ∀ j ω, 1 ≤ A j ω)
    (hK : ∀ j ω, |_root_.GD.N0232.N0720.N1039.d016523 a b (M j ω / A j ω) (c ω)| ≤ K)
    (hLnn : ∀ ω, 0 ≤ L ω)
    (hL : Integrable L ν)
    (hmeas : ∀ j, AEStronglyMeasurable
      (fun ω => _root_.GD.N0232.N0720.N1039.d016521 (A j ω) (c ω) *
        _root_.GD.N0232.N0720.N1039.d016522 a b (M j ω) (A j ω) (c ω) ^ 2 * L ω) ν)
    (hesc : ∀ᵐ ω ∂ν, Tendsto (fun j => A j ω) atTop atTop) :
    Tendsto (fun j => ∫ ω, _root_.GD.N0232.N0720.N1039.d016521 (A j ω) (c ω) *
        _root_.GD.N0232.N0720.N1039.d016522 a b (M j ω) (A j ω) (c ω) ^ 2 * L ω ∂ν) atTop (𝓝 0) := by
  have key : Tendsto (fun j => ∫ ω, _root_.GD.N0232.N0720.N1039.d016521 (A j ω) (c ω) *
      _root_.GD.N0232.N0720.N1039.d016522 a b (M j ω) (A j ω) (c ω) ^ 2 * L ω ∂ν) atTop
      (𝓝 (∫ _ω, (0 : ℝ) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => K ^ 2 * L ω) hmeas (hL.const_mul (K ^ 2)) ?_ ?_
    · intro j
      filter_upwards with ω
      have hnn : 0 ≤ _root_.GD.N0232.N0720.N1039.d016521 (A j ω) (c ω) *
          _root_.GD.N0232.N0720.N1039.d016522 a b (M j ω) (A j ω) (c ω) ^ 2 * L ω :=
        mul_nonneg
          (_root_.GD.N0232.N0720.N1039.d016527 (hA1 j ω) (hc ω)) (hLnn ω)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hbound := _root_.GD.N0232.N0720.N1039.d016529
        (hA1 j ω) (hc ω) (hK j ω)
      exact mul_le_mul_of_nonneg_right hbound (hLnn ω)
    · filter_upwards [hesc] with ω hω
      have hpt := _root_.GD.N0232.N0720.N1039.d016532 (c := c ω) (hc ω)
        (fun j => hA1 j ω) (fun j => hK j ω) hω
      simpa using hpt.mul_const (L ω)
  simpa using key



open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false




theorem d016539
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016416
          (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight (g • omega) -
        g • _root_.GD.N0232.N0720.N1126.d016416 packet weight omega =
      _root_.GD.N0232.N0720.N1039.d016522 g.d009239 g.shift
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) := by
  rw [_root_.GD.N0232.N0720.N1124.d016510 g packet weight hweight omega]
  rfl



theorem d016540
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    1 ≤ _root_.GD.N0232.N0720.N1126.d016415 (m := m) (n := n) packet weight omega :=
  _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
    (_root_.GD.N0232.N0720.N1126.d016419 packet) omega



theorem d016541
    (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 < _root_.GD.N0232.N0720.N1499.d015001 m n
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
  _root_.GD.N0232.N0720.N1499.d015005 m n _ _



theorem d016542
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1039.d016523 g.d009239 g.shift
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
            (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) =
      g.d009239 *
          _root_.GD.N0232.N0720.N1126.d016416 (m := m) (n := n) packet weight omega *
          (_root_.GD.N0232.N0720.N1499.d015001 m n
            (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) -
        g.shift := by
  rfl

end

end N1039
end N0720
end N0232
end GD
