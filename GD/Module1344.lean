import GD.Module1343






set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory

namespace GD.N0106.N0428.N0770.N1747
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0933 _root_.GD.N0106.N0428.N0770.N1753 _root_.GD.N0106.N0428.N0770.N1750

def d021769 (k : ℕ) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k (fun _ => 2)) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0900.d009104 k (fun _ => 2) omega) i

theorem d021770 (k : ℕ) (i : Fin k) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1747.d021769 k i) :=
  (_root_.GD.N0232.N0719.N0900.d009117 i).comp
    (_root_.GD.N0232.N0719.N0900.d009115 k (fun _ => 2))

theorem d021771 (k : ℕ) (i : Fin k)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k (fun _ => 2)) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega := _root_.GD.N0232.N0719.N0900.d009129 _ i




theorem d021772 {k : ℕ} (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (F : (Fin k → ℝ) → ℝ) (hF : Measurable F) :
    (∫ omega, F (fun i => _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega)
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      ∫ z, F (fun i => _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i z) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k) := by
  let g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ := fun s => F (fun i => _root_.GD.N0232.N0719.N0900.d009106 s i)
  have hg : Measurable g :=
    hF.comp (measurable_pi_lambda _ (fun i => _root_.GD.N0232.N0719.N0900.d009117 i))
  let f : (Fin k → ℝ) → ℝ := fun t => g (_root_.GD.N0232.N0719.N0933.d009305 k (0, t))
  have hf : Measurable f := hg.comp ((_root_.GD.N0232.N0719.N0933.d009306 k).comp
    (measurable_const.prodMk measurable_id))
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009300 k (fun _ => 2) mu sigma) := by
    rw [_root_.GD.N0232.N0719.N0933.d009302 k (fun _ => 2) (fun _ => le_rfl)]
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma) := by
    rw [← _root_.GD.N0106.N0428.N0770.N1753.d021762 sigma]
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0106.N0428.N0770.N1753.d021760 sigma).aemeasurable
  calc
    _ = ∫ s, g (_root_.GD.N0232.N0719.N0933.d009305 k s)
        ∂(_root_.GD.N0232.N0719.N0933.d009300 k (fun _ => 2) mu sigma).prod
          (_root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma) :=
      _root_.GD.N0232.N0719.N0933.d009310 k (fun _ => 2)
        (fun _ => le_rfl) mu sigma g hg
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
      exact _root_.GD.N0106.N0428.N0770.N1753.d021764 sigma 0 z hsigma hz i

theorem d021773 {k : ℕ} (mu : ℝ) (sigma : Fin k → ℝ)
    (i : Fin k) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun omega => _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega ^ n *
      Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega)))
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) :=
  _root_.GD.N0106.N0428.N0770.N1744.d007148 (_root_.GD.N0106.N0428.N0770.N1747.d021770 k i)
    (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1747.d021771 k i)) ht n

theorem d021774 {k : ℕ} (mu : ℝ)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k)
    {t : ℝ} (ht : 0 < t) :
    (∫ omega, Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega))
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma i) t := by
  rw [_root_.GD.N0106.N0428.N0770.N1747.d021772 mu sigma hsigma
    (fun p => Real.exp (-(t * p i))) (by fun_prop)]
  exact _root_.GD.N0106.N0428.N0770.N1750.d008374 hsigma ht i

theorem d021775 {k : ℕ} (mu : ℝ)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k)
    {t : ℝ} (ht : 0 < t) :
    (∫ omega, _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega))
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      _root_.GD.N0106.N0428.N0770.N1744.d008351 (2 / sigma i) t :=
  _root_.GD.N0106.N0428.N0770.N1744.d008355 (_root_.GD.N0106.N0428.N0770.N1747.d021770 k i)
    (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1747.d021771 k i))
    (fun s hs => _root_.GD.N0106.N0428.N0770.N1747.d021774 mu sigma hsigma i hs) ht

theorem d021776 {k : ℕ} (mu : ℝ)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k)
    {t : ℝ} (ht : 0 < t) :
    (∫ omega, _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega ^ 2 * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega))
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) =
      _root_.GD.N0106.N0428.N0770.N1744.d008352 (2 / sigma i) t :=
  _root_.GD.N0106.N0428.N0770.N1744.d008356 (_root_.GD.N0106.N0428.N0770.N1747.d021770 k i)
    (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1747.d021771 k i))
    (fun s hs => _root_.GD.N0106.N0428.N0770.N1747.d021774 mu sigma hsigma i hs) ht


theorem d021777 {k : ℕ} (mu : ℝ)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ omega, Real.exp (-(s * _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega))
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma)
      (-(_root_.GD.N0106.N0428.N0770.N1744.d008351 (2 / sigma i) t)) t := by
  have h := _root_.GD.N0106.N0428.N0770.N1744.d007150 (μ := _root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma)
    (_root_.GD.N0106.N0428.N0770.N1747.d021770 k i) (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1747.d021771 k i)) ht
  rwa [_root_.GD.N0106.N0428.N0770.N1747.d021775 mu sigma hsigma i ht] at h

theorem d021778 {k : ℕ} (mu : ℝ)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) (i : Fin k)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ omega, _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega *
      Real.exp (-(s * _root_.GD.N0106.N0428.N0770.N1747.d021769 k i omega))
      ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma)
      (-(_root_.GD.N0106.N0428.N0770.N1744.d008352 (2 / sigma i) t)) t := by
  have h := _root_.GD.N0106.N0428.N0770.N1744.d007149
    (μ := _root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma)
    (_root_.GD.N0106.N0428.N0770.N1747.d021770 k i) (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1747.d021771 k i)) ht 1
  simpa only [pow_one, Nat.reduceAdd,
    _root_.GD.N0106.N0428.N0770.N1747.d021776 mu sigma hsigma i ht] using h

end
end GD.N0106.N0428.N0770.N1747

#print axioms _root_.GD.N0106.N0428.N0770.N1747.d021772
#print axioms _root_.GD.N0106.N0428.N0770.N1747.d021773
#print axioms _root_.GD.N0106.N0428.N0770.N1747.d021774
#print axioms _root_.GD.N0106.N0428.N0770.N1747.d021775
#print axioms _root_.GD.N0106.N0428.N0770.N1747.d021776
#print axioms _root_.GD.N0106.N0428.N0770.N1747.d021777
#print axioms _root_.GD.N0106.N0428.N0770.N1747.d021778
