import GD.Module1345










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1746
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0933 _root_.GD.N0106.N0428.N0770.N1753 _root_.GD.N0106.N0428.N0770.N1750


def d021809 (k : ℕ) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k (fun _ => 2)) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0900.d009104 k (fun _ => 2) omega) i


def d021810 {k : ℕ} (sigma : Fin k → ℝ) (i : Fin k) : ℝ :=
  (2 / sigma i) / _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma

theorem d021811 (k : ℕ) (i : Fin k) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1746.d021809 k i) :=
  (_root_.GD.N0232.N0719.N0900.d009119 i).comp
    (_root_.GD.N0232.N0719.N0900.d009115 k (fun _ => 2))

theorem d021812 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (i : Fin k) (n : ℕ) :
    Integrable (fun omega => _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega ^ n)
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((_root_.GD.N0106.N0428.N0770.N1746.d021811 k i).pow_const n).aestronglyMeasurable
  filter_upwards with omega
  have hlo : 0 ≤ _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega :=
    _root_.GD.N0232.N0719.N0900.d009132 hk _ i
  have hhi : _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega ≤ 1 :=
    _root_.GD.N0232.N0719.N0900.d009133 hk _ i
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlo n)]
  exact pow_le_one₀ hlo hhi

theorem d021813 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (i : Fin k) :
    MemLp (_root_.GD.N0106.N0428.N0770.N1746.d021809 k i) 2
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) :=
  (memLp_two_iff_integrable_sq
    (_root_.GD.N0106.N0428.N0770.N1746.d021811 k i).aestronglyMeasurable).mpr
      (_root_.GD.N0106.N0428.N0770.N1746.d021812 hk mu sigma i 2)




theorem d021814 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i)
    (F : (Fin k → ℝ) → ℝ) (hF : Measurable F) :
    (∫ omega, F (fun i => _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega)
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      ∫ z, F (fun i => _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i z) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k) := by
  let f : (Fin k → ℝ) → ℝ := fun t =>
    F (_root_.GD.N0232.N0719.N0900.d009109 (_root_.GD.N0232.N0719.N0933.d009305 k (0, t)))
  have hf : Measurable f :=
    hF.comp (_root_.GD.N0232.N0719.N0900.d009120.comp
      ((_root_.GD.N0232.N0719.N0933.d009306 k).comp
        (measurable_const.prodMk measurable_id)))
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009300 k (fun _ => 2) mu sigma) := by
    rw [_root_.GD.N0232.N0719.N0933.d009302 k (fun _ => 2) (fun _ => le_rfl)]
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma) := by
    rw [← _root_.GD.N0106.N0428.N0770.N1753.d021762 sigma]
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0106.N0428.N0770.N1753.d021760 sigma).aemeasurable
  calc
    _ = ∫ s, F (_root_.GD.N0232.N0719.N0900.d009109 (_root_.GD.N0232.N0719.N0933.d009305 k s))
        ∂(_root_.GD.N0232.N0719.N0933.d009300 k (fun _ => 2) mu sigma).prod
          (_root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma) :=
      _root_.GD.N0232.N0719.N0933.d009310 k (fun _ => 2)
        (fun _ => le_rfl) mu sigma (fun s => F (_root_.GD.N0232.N0719.N0900.d009109 s))
        (hF.comp _root_.GD.N0232.N0719.N0900.d009120)
    _ = ∫ s, f s.2 ∂(_root_.GD.N0232.N0719.N0933.d009300 k (fun _ => 2) mu sigma).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma) := rfl
    _ = ∫ t, f t ∂_root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma := by
      rw [integral_fun_snd]
      simp
    _ = ∫ z, f (_root_.GD.N0106.N0428.N0770.N1753.d021759 sigma z) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k) := by
      rw [← _root_.GD.N0106.N0428.N0770.N1753.d021762 sigma,
        integral_map_of_stronglyMeasurable (_root_.GD.N0106.N0428.N0770.N1753.d021760 sigma)
          hf.stronglyMeasurable]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0106.N0428.N0770.N1753.d021767 k] with z hz
      apply congrArg F
      funext i
      exact _root_.GD.N0106.N0428.N0770.N1753.d021765 hk sigma 0 z hsigma hz i

theorem d021815 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k) :
    (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) = _root_.GD.N0106.N0428.N0770.N1746.d021810 sigma i := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [_root_.GD.N0106.N0428.N0770.N1746.d021814 hk mu sigma hsigma (fun w => w i)
    (measurable_pi_apply i)]
  exact _root_.GD.N0106.N0428.N0770.N1750.d008399 hsigma i

theorem d021816 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k) :
    (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega ^ 2
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      (_root_.GD.N0106.N0428.N0770.N1746.d021810 sigma i ^ 2 + _root_.GD.N0106.N0428.N0770.N1746.d021810 sigma i) / 2 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [_root_.GD.N0106.N0428.N0770.N1746.d021814 hk mu sigma hsigma (fun w => w i ^ 2)
    ((measurable_pi_apply i).pow_const 2)]
  exact _root_.GD.N0106.N0428.N0770.N1750.d008400 hsigma i

theorem d021817 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i)
    {i j : Fin k} (hij : i ≠ j) :
    (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega * _root_.GD.N0106.N0428.N0770.N1746.d021809 k j omega
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      _root_.GD.N0106.N0428.N0770.N1746.d021810 sigma i * _root_.GD.N0106.N0428.N0770.N1746.d021810 sigma j / 2 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [_root_.GD.N0106.N0428.N0770.N1746.d021814 hk mu sigma hsigma (fun w => w i * w j)
    ((measurable_pi_apply i).mul (measurable_pi_apply j)),
    _root_.GD.N0106.N0428.N0770.N1750.d008401 hsigma hij]
  unfold _root_.GD.N0106.N0428.N0770.N1746.d021810
  field_simp [(_root_.GD.N0106.N0428.N0770.N1750.d008394 hsigma).ne', (hsigma i).ne', (hsigma j).ne']
  <;> ring

theorem d021818 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i)
    {i j : Fin k} (hij : i ≠ j) :
    covariance (_root_.GD.N0106.N0428.N0770.N1746.d021809 k i) (_root_.GD.N0106.N0428.N0770.N1746.d021809 k j)
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      -(_root_.GD.N0106.N0428.N0770.N1746.d021810 sigma i * _root_.GD.N0106.N0428.N0770.N1746.d021810 sigma j) / 2 := by
  rw [covariance_eq_sub (_root_.GD.N0106.N0428.N0770.N1746.d021813 hk mu sigma i)
    (_root_.GD.N0106.N0428.N0770.N1746.d021813 hk mu sigma j)]
  change (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega * _root_.GD.N0106.N0428.N0770.N1746.d021809 k j omega
    ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) -
      (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) *
      (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k j omega ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) = _
  rw [_root_.GD.N0106.N0428.N0770.N1746.d021817 hk mu sigma hsigma hij,
    _root_.GD.N0106.N0428.N0770.N1746.d021815 hk mu sigma hsigma i,
    _root_.GD.N0106.N0428.N0770.N1746.d021815 hk mu sigma hsigma j]
  ring

theorem d021819 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k) :
    covariance (_root_.GD.N0106.N0428.N0770.N1746.d021809 k i) (_root_.GD.N0106.N0428.N0770.N1746.d021809 k i)
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      _root_.GD.N0106.N0428.N0770.N1746.d021810 sigma i * (1 - _root_.GD.N0106.N0428.N0770.N1746.d021810 sigma i) / 2 := by
  rw [covariance_eq_sub (_root_.GD.N0106.N0428.N0770.N1746.d021813 hk mu sigma i)
    (_root_.GD.N0106.N0428.N0770.N1746.d021813 hk mu sigma i)]
  change (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega * _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega
    ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) -
      (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) *
      (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) = _
  simp_rw [← sq]
  rw [_root_.GD.N0106.N0428.N0770.N1746.d021816 hk mu sigma hsigma i,
    _root_.GD.N0106.N0428.N0770.N1746.d021815 hk mu sigma hsigma i]
  ring



theorem d021820 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta =
      ∑ i, theta.scale i ^ 2 / 2 *
        (∫ omega, _root_.GD.N0106.N0428.N0770.N1746.d021809 k i omega ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) theta.location theta.scale) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021782 hk,
    ← _root_.GD.N0106.N0428.N0770.N1750.d008407 hk theta.scale_pos]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0106.N0428.N0770.N1750.d008400 theta.scale_pos i,
    _root_.GD.N0106.N0428.N0770.N1746.d021816 hk theta.location theta.scale theta.scale_pos i]
  rfl

end
end GD.N0106.N0428.N0770.N1746

#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021811
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021812
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021813
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021814
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021815
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021816
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021817
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021818
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021819
#print axioms _root_.GD.N0106.N0428.N0770.N1746.d021820
