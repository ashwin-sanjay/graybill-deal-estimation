import GD.Module0637









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1751
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0933


def d021738 (mu sigma : ℝ) (x : _root_.GD.N0137.d008894 2) : ℝ × ℝ :=
  ((x 0 + x 1 - 2 * mu) / (Real.sqrt 2 * sigma),
    (x 0 - x 1) / (Real.sqrt 2 * sigma))

@[fun_prop] theorem d021739 (mu sigma : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1751.d021738 mu sigma) := by
  unfold _root_.GD.N0106.N0428.N0770.N1751.d021738
  fun_prop

theorem d021740 (mu sigma : ℝ) (hsigma : 0 < sigma)
    (z : _root_.GD.N0137.d008894 2) :
    _root_.GD.N0106.N0428.N0770.N1751.d021738 mu sigma (_root_.GD.N0107.d009018 2 mu sigma z) =
      _root_.GD.N0137.d008920 (1 / 2) (z 0, z 1) := by
  have hhalf : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  unfold _root_.GD.N0106.N0428.N0770.N1751.d021738 _root_.GD.N0107.d009018 _root_.GD.N0137.d008920
    _root_.GD.N0137.d008918 _root_.GD.N0137.d008919
  simp only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hhalf]
  apply Prod.ext <;> dsimp <;> field_simp [hsigma.ne', hsqrt] <;> ring



theorem d021741 (mu sigma : ℝ) (hsigma : 0 < sigma) :
    (_root_.GD.N0232.N0719.d009174 2 mu sigma).map (_root_.GD.N0106.N0428.N0770.N1751.d021738 mu sigma) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  unfold _root_.GD.N0232.N0719.d009174
  rw [Measure.map_map (_root_.GD.N0106.N0428.N0770.N1751.d021739 mu sigma)
    (_root_.GD.N0107.d009020 2 mu sigma)]
  have heq : _root_.GD.N0106.N0428.N0770.N1751.d021738 mu sigma ∘ _root_.GD.N0107.d009018 2 mu sigma =
      _root_.GD.N0137.d008920 (1 / 2) ∘
        (MeasurableEquiv.finTwoArrow : _root_.GD.N0137.d008894 2 ≃ᵐ ℝ × ℝ) := by
    funext z
    exact _root_.GD.N0106.N0428.N0770.N1751.d021740 mu sigma hsigma z
  rw [heq, ← Measure.map_map (_root_.GD.N0137.d008921 (1 / 2))
    MeasurableEquiv.finTwoArrow.measurable]
  have hpair : (_root_.GD.N0137.d008895 2).map MeasurableEquiv.finTwoArrow =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    exact (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [hpair]
  exact _root_.GD.N0137.d008927 (by norm_num) (by norm_num)

def d021742 (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => gaussianReal 0 1)

instance d021743 (k : ℕ) :
    IsProbabilityMeasure (_root_.GD.N0106.N0428.N0770.N1751.d021742 k) := by
  unfold _root_.GD.N0106.N0428.N0770.N1751.d021742
  infer_instance


def d021744 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (omega : _root_.GD.N0232.N0719.d009173 k (fun _ => 2)) : (Fin k → ℝ) × (Fin k → ℝ) :=
  ((fun i => (_root_.GD.N0106.N0428.N0770.N1751.d021738 mu (sigma i) (omega i)).1),
    (fun i => (_root_.GD.N0106.N0428.N0770.N1751.d021738 mu (sigma i) (omega i)).2))

@[fun_prop] theorem d021745 (k : ℕ) (mu : ℝ)
    (sigma : Fin k → ℝ) : Measurable (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma) := by
  unfold _root_.GD.N0106.N0428.N0770.N1751.d021744
  fun_prop



theorem d021746 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
      (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma) =
        (_root_.GD.N0106.N0428.N0770.N1751.d021742 k).prod (_root_.GD.N0106.N0428.N0770.N1751.d021742 k) := by
  change (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
    (_root_.GD.N0232.N0719.N0933.d009299 k ∘ (fun omega i => _root_.GD.N0106.N0428.N0770.N1751.d021738 mu (sigma i) (omega i))) = _
  rw [← Measure.map_map (_root_.GD.N0232.N0719.N0933.d009299 k).measurable
    (by fun_prop : Measurable (fun (omega : _root_.GD.N0232.N0719.d009173 k (fun _ => 2)) i =>
      _root_.GD.N0106.N0428.N0770.N1751.d021738 mu (sigma i) (omega i)))]
  unfold _root_.GD.N0232.N0719.d009176
  rw [Measure.pi_map_pi (fun i => (_root_.GD.N0106.N0428.N0770.N1751.d021739 mu (sigma i)).aemeasurable)]
  simp_rw [_root_.GD.N0106.N0428.N0770.N1751.d021741 mu _ (hsigma _)]
  exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin k)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).map_eq

theorem d021747 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
      (fun omega => (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).1) = _root_.GD.N0106.N0428.N0770.N1751.d021742 k := by
  change (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
    (Prod.fst ∘ _root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma) = _root_.GD.N0106.N0428.N0770.N1751.d021742 k
  rw [← Measure.map_map measurable_fst (_root_.GD.N0106.N0428.N0770.N1751.d021745 k mu sigma),
    _root_.GD.N0106.N0428.N0770.N1751.d021746 k mu sigma hsigma, Measure.map_fst_prod]
  simp

theorem d021748 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
      (fun omega => (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).2) = _root_.GD.N0106.N0428.N0770.N1751.d021742 k := by
  change (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
    (Prod.snd ∘ _root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma) = _root_.GD.N0106.N0428.N0770.N1751.d021742 k
  rw [← Measure.map_map measurable_snd (_root_.GD.N0106.N0428.N0770.N1751.d021745 k mu sigma),
    _root_.GD.N0106.N0428.N0770.N1751.d021746 k mu sigma hsigma, Measure.map_snd_prod]
  simp

theorem d021749 (k : ℕ) (mu : ℝ)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) :
    IndepFun (fun omega => (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).1)
      (fun omega => (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).2)
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (_root_.GD.N0106.N0428.N0770.N1751.d021745 k mu sigma).fst.aemeasurable
    (_root_.GD.N0106.N0428.N0770.N1751.d021745 k mu sigma).snd.aemeasurable).mpr
  rw [_root_.GD.N0106.N0428.N0770.N1751.d021747 k mu sigma hsigma, _root_.GD.N0106.N0428.N0770.N1751.d021748 k mu sigma hsigma]
  exact _root_.GD.N0106.N0428.N0770.N1751.d021746 k mu sigma hsigma


theorem d021750 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ) :
    iIndepFun (fun i omega => (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).2 i)
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) :=
  iIndepFun_pi (μ := fun i => _root_.GD.N0232.N0719.d009174 2 mu (sigma i))
    (X := fun i x => (_root_.GD.N0106.N0428.N0770.N1751.d021738 mu (sigma i) x).2)
    (fun i => (_root_.GD.N0106.N0428.N0770.N1751.d021739 mu (sigma i)).snd.aemeasurable)

theorem d021751 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (i : Fin k) :
    (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
      (fun omega => (omega i 0 - omega i 1) / (Real.sqrt 2 * sigma i)) =
        gaussianReal 0 1 := by
  change (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
    ((fun z : Fin k → ℝ => z i) ∘ (fun omega => (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).2)) = _
  rw [← Measure.map_map (measurable_pi_apply i)
    (_root_.GD.N0106.N0428.N0770.N1751.d021745 k mu sigma).snd, _root_.GD.N0106.N0428.N0770.N1751.d021748 k mu sigma hsigma]
  exact (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) i).map_eq


theorem d021752 (mu sigma : ℝ) (hsigma : 0 < sigma)
    (x : _root_.GD.N0137.d008894 2) :
    _root_.GD.N0107.d009084 x = mu + sigma * (_root_.GD.N0106.N0428.N0770.N1751.d021738 mu sigma x).1 / Real.sqrt 2 := by
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  unfold _root_.GD.N0107.d009084 _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
    _root_.GD.N0106.N0428.N0770.N1751.d021738
  simp only [Fin.sum_univ_two, Fintype.card_fin, Nat.cast_ofNat]
  field_simp [hsigma.ne', hsqrt]
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt]
  <;> ring



theorem d021753 (mu sigma : ℝ) (hsigma : 0 < sigma)
    (x : _root_.GD.N0137.d008894 2) :
    _root_.GD.N0107.d009085 x / 2 = sigma ^ 2 * (_root_.GD.N0106.N0428.N0770.N1751.d021738 mu sigma x).2 ^ 2 / 2 := by
  unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419 _root_.GD.N0106.N0428.N0770.N1751.d021738
  simp only [Fin.sum_univ_two, Fintype.card_fin, Nat.cast_ofNat, Nat.reduceSub, Nat.cast_one,
    div_one, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [hsigma.ne']
  <;> ring


def d021754 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (p : (Fin k → ℝ) × (Fin k → ℝ)) : (Fin k → ℝ) × (Fin k → ℝ) :=
  ((fun i => mu + sigma i * p.1 i / Real.sqrt 2),
    (fun i => sigma i ^ 2 * p.2 i ^ 2 / 2))

@[fun_prop] theorem d021755 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1751.d021754 k mu sigma) := by
  unfold _root_.GD.N0106.N0428.N0770.N1751.d021754
  fun_prop

theorem d021756 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (omega : _root_.GD.N0232.N0719.d009173 k (fun _ => 2)) :
    _root_.GD.N0106.N0428.N0770.N1751.d021754 k mu sigma (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega) =
      _root_.GD.N0232.N0719.N0933.d009304 k (fun _ => 2) omega := by
  apply Prod.ext <;> funext i
  · exact (_root_.GD.N0106.N0428.N0770.N1751.d021752 mu (sigma i) (hsigma i) (omega i)).symm
  · exact (_root_.GD.N0106.N0428.N0770.N1751.d021753 mu (sigma i) (hsigma i) (omega i)).symm



theorem d021757 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    ((_root_.GD.N0106.N0428.N0770.N1751.d021742 k).prod (_root_.GD.N0106.N0428.N0770.N1751.d021742 k)).map (_root_.GD.N0106.N0428.N0770.N1751.d021754 k mu sigma) =
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
        (_root_.GD.N0232.N0719.N0933.d009304 k (fun _ => 2)) := by
  rw [← _root_.GD.N0106.N0428.N0770.N1751.d021746 k mu sigma hsigma,
    Measure.map_map (_root_.GD.N0106.N0428.N0770.N1751.d021755 k mu sigma)
      (_root_.GD.N0106.N0428.N0770.N1751.d021745 k mu sigma)]
  congr 1
  funext omega
  exact _root_.GD.N0106.N0428.N0770.N1751.d021756 k mu sigma hsigma omega


theorem d021758 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    IndepFun (fun omega i => _root_.GD.N0107.d009084 (omega i))
      (fun omega i => (omega i 0 - omega i 1) / (Real.sqrt 2 * sigma i))
      (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma) := by
  change IndepFun (fun omega i => _root_.GD.N0107.d009084 (omega i))
    (fun omega => (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).2)
    (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma)
  have h := (_root_.GD.N0106.N0428.N0770.N1751.d021749 k mu sigma hsigma).comp
    (by fun_prop : Measurable (fun u : Fin k → ℝ => fun i =>
      mu + sigma i * u i / Real.sqrt 2)) measurable_id
  have heq : (fun omega => (fun u : Fin k → ℝ => fun i =>
      mu + sigma i * u i / Real.sqrt 2) (_root_.GD.N0106.N0428.N0770.N1751.d021744 k mu sigma omega).1) =
      (fun omega i => _root_.GD.N0107.d009084 (omega i)) := by
    funext omega i
    exact (_root_.GD.N0106.N0428.N0770.N1751.d021752 mu (sigma i) (hsigma i) (omega i)).symm
  simpa only [Function.comp_def, heq, id_eq] using h

end
end GD.N0106.N0428.N0770.N1751

#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021740
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021741
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021746
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021747
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021748
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021749
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021750
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021751
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021752
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021753
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021756
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021757
#print axioms _root_.GD.N0106.N0428.N0770.N1751.d021758
