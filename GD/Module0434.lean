import GD.Module0178
import GD.Module0274

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0101.N0369
noncomputable section

open _root_.GD.N0232.N0720.N1242


def d006733 (δ : ℝ) : ℝ :=
  (_root_.GD.N0232.N0720.N1242.d002139 (Ioo δ (1 - δ))).toReal

theorem d006734 (δ : ℝ) : 0 ≤ _root_.GD.N0101.N0369.d006733 δ :=
  ENNReal.toReal_nonneg

theorem d006735 (δ : ℝ) : _root_.GD.N0101.N0369.d006733 δ ≤ 1 := by
  letI := _root_.GD.N0232.N0720.N1242.d002140
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one :
    _root_.GD.N0232.N0720.N1242.d002139 (Ioo δ (1 - δ)) ≤ 1)).trans_eq (by simp)

theorem d006736 (δ : ℝ) :
    _root_.GD.N0101.N0369.d006733 δ =
      ∫ u in Ioo δ (1 - δ), betaPDFReal (1 / 2 : ℝ) (1 / 2) u := by
  unfold _root_.GD.N0101.N0369.d006733 _root_.GD.N0232.N0720.N1242.d002139 betaMeasure
  rw [withDensity_apply _ measurableSet_Ioo]
  symm
  exact integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun u => _root_.GD.N0235.d004040
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) u))
    (measurable_betaPDFReal _ _).aestronglyMeasurable



theorem d006737 {δ : ℝ} (hδ : 0 < δ) :
    _root_.GD.N0101.N0369.d006733 δ =
      ∫ u in Ioo δ (1 - δ), 1 / (Real.pi * Real.sqrt (u * (1 - u))) := by
  rw [_root_.GD.N0101.N0369.d006736]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact _root_.GD.N0232.N0720.N1242.d002142 ⟨hδ.trans hu.1, by linarith [hu.2]⟩



theorem d006738 {q : ℝ} (hq : q < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ q < _root_.GD.N0101.N0369.d006733 δ := by
  letI := _root_.GD.N0232.N0720.N1242.d002140
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let s : ℕ → Set ℝ := fun n => Ioo (d n) (1 - d n)
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdanti : Antitone d := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hsmono : Monotone s := by
    intro i j hij x hx
    exact ⟨(hdanti hij).trans_lt hx.1, hx.2.trans_le (by linarith [hdanti hij])⟩
  have hunion : (⋃ n, s n) = Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact ⟨(hdpos n).trans hn.1, by linarith [hn.2, hdpos n]⟩
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hx.1 (sub_pos.mpr hx.2))
      exact mem_iUnion.mpr ⟨n, ⟨hn.trans_le (min_le_left _ _),
        by have h := hn.trans_le (min_le_right _ _); dsimp [d]; linarith⟩⟩
  have hae : Ioo (0 : ℝ) 1 =ᵐ[_root_.GD.N0232.N0720.N1242.d002139] univ := by
    filter_upwards [_root_.GD.N0232.N0720.N1242.d002141] with x hx
    exact propext ⟨fun _ => trivial, fun _ => hx⟩
  have hfull : _root_.GD.N0232.N0720.N1242.d002139 (Ioo (0 : ℝ) 1) = 1 := by
    rw [measure_congr hae]
    simp
  have hsup : (⨆ n : ℕ, _root_.GD.N0232.N0720.N1242.d002139 (s n)) = 1 := by
    rw [← hsmono.measure_iUnion, hunion, hfull]
  have hqmax : max q 0 < 1 := max_lt hq (by norm_num)
  have hlarge : ENNReal.ofReal (max q 0) < ⨆ n : ℕ, _root_.GD.N0232.N0720.N1242.d002139 (s n) := by
    rw [hsup]
    exact ENNReal.ofReal_lt_one.mpr hqmax
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hlarge
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (bot_le.trans_lt hn).ne'
  refine ⟨d n, hdpos n, ?_, ?_⟩
  · have hx' : d n < x ∧ x < 1 - d n := hx
    linarith
  · exact (le_max_left q 0).trans_lt
      ((ENNReal.ofReal_lt_iff_lt_toReal (le_max_right q 0) (measure_ne_top _ _)).mp hn)

end
end GD.N0101.N0369

#print axioms _root_.GD.N0101.N0369.d006735
#print axioms _root_.GD.N0101.N0369.d006736
#print axioms _root_.GD.N0101.N0369.d006737
#print axioms _root_.GD.N0101.N0369.d006738
