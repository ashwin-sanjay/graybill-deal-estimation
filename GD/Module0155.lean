import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
































open Real Set MeasureTheory

namespace GD.N0232.N0719.N0878

noncomputable def d001740 (rate x : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-rate * x))

lemma d001741 (rate u : ℝ) (hrate : 0 < rate) :
    ∫⁻ x in Ioi u, _root_.GD.N0232.N0719.N0878.d001740 rate x =
      ENNReal.ofReal (Real.exp (-rate * u) / rate) := by
  simp only [_root_.GD.N0232.N0719.N0878.d001740]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    convert integral_exp_mul_Ioi (a := -rate) (by linarith) u using 1
    all_goals simp [neg_mul]
  · exact integrableOn_exp_mul_Ioi (by linarith) u
  · exact Filter.Eventually.of_forall fun x ↦ Real.exp_pos _ |>.le

lemma d001742 (rate u : ℝ) (hrate : 0 < rate) :
    ∫⁻ x in Ici u, _root_.GD.N0232.N0719.N0878.d001740 rate x =
      ENNReal.ofReal (Real.exp (-rate * u) / rate) := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  exact _root_.GD.N0232.N0719.N0878.d001741 rate u hrate

def d001743 : Set (ℝ × ℝ) :=
  {z | 0 < z.1 ∧ 0 < z.2 ∧ z.2 ≤ z.1}

lemma d001744 : MeasurableSet _root_.GD.N0232.N0719.N0878.d001743 := by
  unfold _root_.GD.N0232.N0719.N0878.d001743
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst))

noncomputable def d001745 (rate : ℝ) (f : ℝ → ENNReal) (z : ℝ × ℝ) : ENNReal :=
  _root_.GD.N0232.N0719.N0878.d001743.indicator (fun z ↦ _root_.GD.N0232.N0719.N0878.d001740 rate z.1 * f z.2) z

lemma d001746 (rate : ℝ) {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (_root_.GD.N0232.N0719.N0878.d001745 rate f) := by
  apply Measurable.indicator _ _root_.GD.N0232.N0719.N0878.d001744
  apply Measurable.mul
  · unfold _root_.GD.N0232.N0719.N0878.d001740
    fun_prop
  · exact hf.comp measurable_snd

theorem d001747 (f : ℝ → ENNReal) (hf : Measurable f)
    (rate : ℝ) (hrate : 0 < rate) :
    (∫⁻ x in Ioi (0 : ℝ), _root_.GD.N0232.N0719.N0878.d001740 rate x * (∫⁻ u in Ioc 0 x, f u)) =
      ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-rate * u) / rate) * f u := by
  calc
    (∫⁻ x in Ioi (0 : ℝ), _root_.GD.N0232.N0719.N0878.d001740 rate x * (∫⁻ u in Ioc 0 x, f u)) =
        ∫⁻ x, ∫⁻ u, _root_.GD.N0232.N0719.N0878.d001745 rate f (x, u) := by
          rw [← lintegral_indicator measurableSet_Ioi]
          apply lintegral_congr
          intro x
          by_cases hx : x ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem hx, ← lintegral_indicator measurableSet_Ioc]
            rw [← lintegral_const_mul'' (_root_.GD.N0232.N0719.N0878.d001740 rate x)
              (hf.indicator measurableSet_Ioc).aemeasurable]
            apply lintegral_congr
            intro u
            by_cases hu : u ∈ Ioc (0 : ℝ) x
            · have hz : (x, u) ∈ _root_.GD.N0232.N0719.N0878.d001743 := ⟨hx, hu.1, hu.2⟩
              simp [_root_.GD.N0232.N0719.N0878.d001745, hu, hz]
            · have hz : (x, u) ∉ _root_.GD.N0232.N0719.N0878.d001743 := by
                intro hz
                exact hu ⟨hz.2.1, hz.2.2⟩
              simp [_root_.GD.N0232.N0719.N0878.d001745, hu, hz]
          · rw [indicator_of_notMem hx]
            symm
            apply lintegral_eq_zero_of_ae_eq_zero
            exact Filter.Eventually.of_forall fun u ↦ by
              have hz : (x, u) ∉ _root_.GD.N0232.N0719.N0878.d001743 := by
                intro hz
                exact hx hz.1
              simp [_root_.GD.N0232.N0719.N0878.d001745, hz]
    _ = ∫⁻ u, ∫⁻ x, _root_.GD.N0232.N0719.N0878.d001745 rate f (x, u) := by
      exact lintegral_lintegral_swap (_root_.GD.N0232.N0719.N0878.d001746 rate hf).aemeasurable
    _ = ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-rate * u) / rate) * f u := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hu]
        have hinner : (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001745 rate f (x, u)) =
            (∫⁻ x in Ici u, _root_.GD.N0232.N0719.N0878.d001740 rate x) * f u := by
          calc
            (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001745 rate f (x, u)) =
                ∫⁻ x in Ici u, _root_.GD.N0232.N0719.N0878.d001740 rate x * f u := by
              rw [← lintegral_indicator measurableSet_Ici]
              apply lintegral_congr
              intro x
              by_cases hx : x ∈ Ici u
              · have hz : (x, u) ∈ _root_.GD.N0232.N0719.N0878.d001743 :=
                  ⟨lt_of_lt_of_le hu hx, hu, hx⟩
                simp [_root_.GD.N0232.N0719.N0878.d001745, hx, hz]
              · have hz : (x, u) ∉ _root_.GD.N0232.N0719.N0878.d001743 := by
                  intro hz
                  exact hx hz.2.2
                simp [_root_.GD.N0232.N0719.N0878.d001745, hx, hz]
            _ = (∫⁻ x in Ici u, _root_.GD.N0232.N0719.N0878.d001740 rate x) * f u := by
              exact lintegral_mul_const'' (f u)
                ((by
                  unfold _root_.GD.N0232.N0719.N0878.d001740
                  fun_prop : Measurable (_root_.GD.N0232.N0719.N0878.d001740 rate)).aemeasurable)
        rw [hinner, _root_.GD.N0232.N0719.N0878.d001742 rate u hrate]
      · rw [indicator_of_notMem hu]
        apply lintegral_eq_zero_of_ae_eq_zero
        exact Filter.Eventually.of_forall fun x ↦ by
          have hz : (x, u) ∉ _root_.GD.N0232.N0719.N0878.d001743 := by
            intro hz
            exact hu hz.2.1
          simp [_root_.GD.N0232.N0719.N0878.d001745, hz]

noncomputable def d001748 (shape x : ℝ) : ENNReal :=
  ENNReal.ofReal (x ^ (shape - 1))

lemma d001749 (shape : ℝ) : Measurable (_root_.GD.N0232.N0719.N0878.d001748 shape) := by
  unfold _root_.GD.N0232.N0719.N0878.d001748
  fun_prop

noncomputable def d001750 (action : ℝ → ℝ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal ((action x) ^ 2)

lemma d001751 {action : ℝ → ℝ} (haction : Measurable action) :
    Measurable (_root_.GD.N0232.N0719.N0878.d001750 action) := by
  unfold _root_.GD.N0232.N0719.N0878.d001750
  fun_prop

noncomputable def d001752
    (shape : ℝ) (action : ℝ → ℝ) (x : ℝ) : ENNReal :=
  _root_.GD.N0232.N0719.N0878.d001748 shape x * _root_.GD.N0232.N0719.N0878.d001750 action x

lemma d001753 (shape : ℝ) {action : ℝ → ℝ}
    (haction : Measurable action) : Measurable (_root_.GD.N0232.N0719.N0878.d001752 shape action) := by
  exact (_root_.GD.N0232.N0719.N0878.d001749 shape).mul (_root_.GD.N0232.N0719.N0878.d001751 haction)

noncomputable def d001754
    (shape : ℝ) (action : ℝ → ℝ) (x : ℝ) : ENNReal :=
  ∫⁻ u in Ioc 0 x, _root_.GD.N0232.N0719.N0878.d001752 shape action u

def d001755 : Set (ℝ × ℝ) :=
  {z | 0 < z.2 ∧ z.2 ≤ z.1}

lemma d001756 : MeasurableSet _root_.GD.N0232.N0719.N0878.d001755 := by
  unfold _root_.GD.N0232.N0719.N0878.d001755
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)

noncomputable def d001757
    (shape : ℝ) (action : ℝ → ℝ) (z : ℝ × ℝ) : ENNReal :=
  _root_.GD.N0232.N0719.N0878.d001755.indicator
    (fun z ↦ _root_.GD.N0232.N0719.N0878.d001752 shape action z.2) z

lemma d001758 (shape : ℝ) {action : ℝ → ℝ}
    (haction : Measurable action) : Measurable (_root_.GD.N0232.N0719.N0878.d001757 shape action) := by
  exact ((_root_.GD.N0232.N0719.N0878.d001753 shape haction).comp measurable_snd).indicator
    _root_.GD.N0232.N0719.N0878.d001756

lemma d001759
    (shape : ℝ) (action : ℝ → ℝ) (x : ℝ) :
    _root_.GD.N0232.N0719.N0878.d001754 shape action x = ∫⁻ u, _root_.GD.N0232.N0719.N0878.d001757 shape action (x, u) := by
  rw [_root_.GD.N0232.N0719.N0878.d001754, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ Ioc (0 : ℝ) x
  · have hz : (x, u) ∈ _root_.GD.N0232.N0719.N0878.d001755 := hu
    simp [_root_.GD.N0232.N0719.N0878.d001757, hu, hz]
  · have hz : (x, u) ∉ _root_.GD.N0232.N0719.N0878.d001755 := hu
    simp [_root_.GD.N0232.N0719.N0878.d001757, hu, hz]

lemma d001760 (shape : ℝ) {action : ℝ → ℝ}
    (haction : Measurable action) : Measurable (_root_.GD.N0232.N0719.N0878.d001754 shape action) := by
  have hk := _root_.GD.N0232.N0719.N0878.d001758 shape haction
  have hi : Measurable (fun x ↦ ∫⁻ u, _root_.GD.N0232.N0719.N0878.d001757 shape action (x, u)) :=
    hk.lintegral_prod_right'
  rw [show _root_.GD.N0232.N0719.N0878.d001754 shape action =
      (fun x ↦ ∫⁻ u, _root_.GD.N0232.N0719.N0878.d001757 shape action (x, u)) by
    funext x
    exact _root_.GD.N0232.N0719.N0878.d001759 shape action x]
  exact hi

noncomputable def d001761
    (shape : ℝ) (action : ℝ → ℝ) (x : ℝ) : ENNReal :=
  (Ioi (0 : ℝ)).indicator
    (fun x ↦ (_root_.GD.N0232.N0719.N0878.d001748 shape x)⁻¹ * _root_.GD.N0232.N0719.N0878.d001754 shape action x) x

lemma d001762 (shape : ℝ) {action : ℝ → ℝ}
    (haction : Measurable action) : Measurable (_root_.GD.N0232.N0719.N0878.d001761 shape action) := by
  unfold _root_.GD.N0232.N0719.N0878.d001761
  exact ((_root_.GD.N0232.N0719.N0878.d001749 shape).inv.mul
    (_root_.GD.N0232.N0719.N0878.d001760 shape haction)).indicator measurableSet_Ioi

lemma d001763 {shape x : ℝ} (hx : 0 < x) :
    _root_.GD.N0232.N0719.N0878.d001748 shape x ≠ 0 := by
  rw [_root_.GD.N0232.N0719.N0878.d001748, Ne, ENNReal.ofReal_eq_zero]
  exact not_le_of_gt (Real.rpow_pos_of_pos hx _)

lemma d001764 (shape x : ℝ) : _root_.GD.N0232.N0719.N0878.d001748 shape x ≠ ⊤ := by
  simp [_root_.GD.N0232.N0719.N0878.d001748]

lemma d001765 {shape x : ℝ} (action : ℝ → ℝ)
    (hx : 0 < x) :
    _root_.GD.N0232.N0719.N0878.d001761 shape action x * _root_.GD.N0232.N0719.N0878.d001748 shape x =
      _root_.GD.N0232.N0719.N0878.d001754 shape action x := by
  rw [_root_.GD.N0232.N0719.N0878.d001761,
    indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
  calc
    (_root_.GD.N0232.N0719.N0878.d001748 shape x)⁻¹ * _root_.GD.N0232.N0719.N0878.d001754 shape action x *
        _root_.GD.N0232.N0719.N0878.d001748 shape x =
        ((_root_.GD.N0232.N0719.N0878.d001748 shape x)⁻¹ * _root_.GD.N0232.N0719.N0878.d001748 shape x) *
          _root_.GD.N0232.N0719.N0878.d001754 shape action x := by ac_rfl
    _ = _root_.GD.N0232.N0719.N0878.d001754 shape action x := by
      rw [ENNReal.inv_mul_cancel (_root_.GD.N0232.N0719.N0878.d001763 hx)
        (_root_.GD.N0232.N0719.N0878.d001764 shape x), one_mul]



lemma d001766
    {shape x : ℝ} (action : ℝ → ℝ) (hx : 0 < x) :
    _root_.GD.N0232.N0719.N0878.d001761 shape action x =
      ENNReal.ofReal (x ^ (1 - shape)) *
        ∫⁻ u in Ioc 0 x,
          ENNReal.ofReal (u ^ (shape - 1)) * ENNReal.ofReal ((action u) ^ 2) := by
  rw [_root_.GD.N0232.N0719.N0878.d001761,
    indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
  simp only [_root_.GD.N0232.N0719.N0878.d001754, _root_.GD.N0232.N0719.N0878.d001752, _root_.GD.N0232.N0719.N0878.d001748, _root_.GD.N0232.N0719.N0878.d001750]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hx (shape - 1))]
  congr 1
  rw [← Real.rpow_neg hx.le]
  congr 1
  linarith

lemma d001767 (rate u : ℝ) (hrate : 0 < rate) :
    ENNReal.ofReal (Real.exp (-rate * u) / rate) =
      (ENNReal.ofReal rate)⁻¹ * _root_.GD.N0232.N0719.N0878.d001740 rate u := by
  rw [ENNReal.ofReal_div_of_pos hrate]
  simp only [div_eq_mul_inv, _root_.GD.N0232.N0719.N0878.d001740]
  ac_rfl



theorem d001768
    (shape rate : ℝ) (action : ℝ → ℝ) (haction : Measurable action)
    (hrate : 0 < rate) :
    (∫⁻ x in Ioi (0 : ℝ),
        _root_.GD.N0232.N0719.N0878.d001740 rate x * _root_.GD.N0232.N0719.N0878.d001754 shape action x) =
      (ENNReal.ofReal rate)⁻¹ *
        ∫⁻ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0719.N0878.d001740 rate x * _root_.GD.N0232.N0719.N0878.d001752 shape action x := by
  unfold _root_.GD.N0232.N0719.N0878.d001754
  rw [_root_.GD.N0232.N0719.N0878.d001747 (_root_.GD.N0232.N0719.N0878.d001752 shape action)
    (_root_.GD.N0232.N0719.N0878.d001753 shape haction) rate hrate]
  rw [← lintegral_const_mul'' (ENNReal.ofReal rate)⁻¹
    (((by
      unfold _root_.GD.N0232.N0719.N0878.d001740
      fun_prop : Measurable (_root_.GD.N0232.N0719.N0878.d001740 rate)).mul
        (_root_.GD.N0232.N0719.N0878.d001753 shape haction)).aemeasurable)]
  apply lintegral_congr
  intro u
  rw [_root_.GD.N0232.N0719.N0878.d001767 rate u hrate]
  ac_rfl

noncomputable def d001769 (shape rate : ℝ) : ENNReal :=
  ENNReal.ofReal (rate ^ shape / Real.Gamma shape)

lemma d001770 {shape rate x : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hx : 0 < x) :
    ProbabilityTheory.gammaPDF shape rate x =
      _root_.GD.N0232.N0719.N0878.d001769 shape rate * _root_.GD.N0232.N0719.N0878.d001748 shape x * _root_.GD.N0232.N0719.N0878.d001740 rate x := by
  rw [ProbabilityTheory.gammaPDF_of_nonneg hx.le]
  simp only [_root_.GD.N0232.N0719.N0878.d001769, _root_.GD.N0232.N0719.N0878.d001748, _root_.GD.N0232.N0719.N0878.d001740]
  rw [ENNReal.ofReal_mul
      (mul_nonneg (by positivity : 0 ≤ rate ^ shape / Real.Gamma shape)
        (by positivity : 0 ≤ x ^ (shape - 1))),
    ENNReal.ofReal_mul (by positivity : 0 ≤ rate ^ shape / Real.Gamma shape)]
  simp [neg_mul]

lemma d001771 (shape rate : ℝ) :
    Measurable (ProbabilityTheory.gammaPDF shape rate) :=
  (ProbabilityTheory.measurable_gammaPDFReal shape rate).ennreal_ofReal

lemma d001772
    (shape rate : ℝ) (action : ℝ → ℝ) (haction : Measurable action)
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001761 shape action x
      ∂ProbabilityTheory.gammaMeasure shape rate) =
      _root_.GD.N0232.N0719.N0878.d001769 shape rate *
        ∫⁻ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0719.N0878.d001740 rate x * _root_.GD.N0232.N0719.N0878.d001754 shape action x := by
  rw [ProbabilityTheory.gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul volume (_root_.GD.N0232.N0719.N0878.d001771 shape rate)
      (_root_.GD.N0232.N0719.N0878.d001762 shape haction)]
  rw [← lintegral_indicator measurableSet_Ioi]
  rw [← lintegral_const_mul'' (_root_.GD.N0232.N0719.N0878.d001769 shape rate)
    (((by
      unfold _root_.GD.N0232.N0719.N0878.d001740
      fun_prop : Measurable (_root_.GD.N0232.N0719.N0878.d001740 rate)).mul
        (_root_.GD.N0232.N0719.N0878.d001760 shape haction)).indicator measurableSet_Ioi).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  change ProbabilityTheory.gammaPDF shape rate x *
      _root_.GD.N0232.N0719.N0878.d001761 shape action x = _
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hxnot : x ∉ Ioi (0 : ℝ) := not_lt_of_ge hxneg.le
    simp [ProbabilityTheory.gammaPDF_of_neg hxneg, hxnot]
  · rw [_root_.GD.N0232.N0719.N0878.d001770 hshape hrate hxpos,
      indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hxpos)]
    calc
      _root_.GD.N0232.N0719.N0878.d001769 shape rate * _root_.GD.N0232.N0719.N0878.d001748 shape x * _root_.GD.N0232.N0719.N0878.d001740 rate x *
          _root_.GD.N0232.N0719.N0878.d001761 shape action x =
          _root_.GD.N0232.N0719.N0878.d001769 shape rate * _root_.GD.N0232.N0719.N0878.d001740 rate x *
            (_root_.GD.N0232.N0719.N0878.d001761 shape action x * _root_.GD.N0232.N0719.N0878.d001748 shape x) := by ac_rfl
      _ = _root_.GD.N0232.N0719.N0878.d001769 shape rate *
          (_root_.GD.N0232.N0719.N0878.d001740 rate x * _root_.GD.N0232.N0719.N0878.d001754 shape action x) := by
        rw [_root_.GD.N0232.N0719.N0878.d001765 action hxpos]
        exact mul_assoc _ _ _

lemma d001773
    (shape rate : ℝ) (action : ℝ → ℝ) (haction : Measurable action)
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001750 action x
      ∂ProbabilityTheory.gammaMeasure shape rate) =
      _root_.GD.N0232.N0719.N0878.d001769 shape rate *
        ∫⁻ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0719.N0878.d001740 rate x * _root_.GD.N0232.N0719.N0878.d001752 shape action x := by
  rw [ProbabilityTheory.gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul volume (_root_.GD.N0232.N0719.N0878.d001771 shape rate)
      (_root_.GD.N0232.N0719.N0878.d001751 haction)]
  rw [← lintegral_indicator measurableSet_Ioi]
  rw [← lintegral_const_mul'' (_root_.GD.N0232.N0719.N0878.d001769 shape rate)
    (((by
      unfold _root_.GD.N0232.N0719.N0878.d001740
      fun_prop : Measurable (_root_.GD.N0232.N0719.N0878.d001740 rate)).mul
        (_root_.GD.N0232.N0719.N0878.d001753 shape haction)).indicator
          measurableSet_Ioi).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  change ProbabilityTheory.gammaPDF shape rate x * _root_.GD.N0232.N0719.N0878.d001750 action x = _
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hxnot : x ∉ Ioi (0 : ℝ) := not_lt_of_ge hxneg.le
    simp [ProbabilityTheory.gammaPDF_of_neg hxneg, hxnot]
  · rw [_root_.GD.N0232.N0719.N0878.d001770 hshape hrate hxpos,
      indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hxpos)]
    unfold _root_.GD.N0232.N0719.N0878.d001752
    ac_rfl








theorem d001774
    (shape rate : ℝ) (action : ℝ → ℝ) (haction : Measurable action)
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001761 shape action x
      ∂ProbabilityTheory.gammaMeasure shape rate) =
      (ENNReal.ofReal rate)⁻¹ *
        ∫⁻ x, _root_.GD.N0232.N0719.N0878.d001750 action x
          ∂ProbabilityTheory.gammaMeasure shape rate := by
  rw [_root_.GD.N0232.N0719.N0878.d001772 shape rate action haction hshape hrate,
    _root_.GD.N0232.N0719.N0878.d001773 shape rate action haction hshape hrate,
    _root_.GD.N0232.N0719.N0878.d001768 shape rate action haction hrate]
  ac_rfl




theorem d001775
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (shape rate : ℝ) (action : Omega → ℝ → ℝ)
    (haction : ∀ omega, Measurable (action omega))
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫⁻ omega, ∫⁻ x, _root_.GD.N0232.N0719.N0878.d001761 shape (action omega) x
      ∂ProbabilityTheory.gammaMeasure shape rate ∂mu) =
      (ENNReal.ofReal rate)⁻¹ *
        ∫⁻ omega, ∫⁻ x, _root_.GD.N0232.N0719.N0878.d001750 (action omega) x
          ∂ProbabilityTheory.gammaMeasure shape rate ∂mu := by
  calc
    (∫⁻ omega, ∫⁻ x, _root_.GD.N0232.N0719.N0878.d001761 shape (action omega) x
        ∂ProbabilityTheory.gammaMeasure shape rate ∂mu) =
        ∫⁻ omega, (ENNReal.ofReal rate)⁻¹ *
          (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001750 (action omega) x
            ∂ProbabilityTheory.gammaMeasure shape rate) ∂mu := by
      apply lintegral_congr
      intro omega
      exact _root_.GD.N0232.N0719.N0878.d001774 shape rate (action omega)
        (haction omega) hshape hrate
    _ = (ENNReal.ofReal rate)⁻¹ *
        ∫⁻ omega, ∫⁻ x, _root_.GD.N0232.N0719.N0878.d001750 (action omega) x
          ∂ProbabilityTheory.gammaMeasure shape rate ∂mu := by
      apply lintegral_const_mul'
      simp [ENNReal.ofReal_eq_zero, not_le_of_gt hrate]

end GD.N0232.N0719.N0878

#print axioms _root_.GD.N0232.N0719.N0878.d001747
#print axioms _root_.GD.N0232.N0719.N0878.d001766
#print axioms _root_.GD.N0232.N0719.N0878.d001774
#print axioms _root_.GD.N0232.N0719.N0878.d001775
