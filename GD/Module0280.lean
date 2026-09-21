import GD.Module0279
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral













open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

namespace GD.N0232.N0720.N1292

open _root_.GD.N0232.N0720.N1290

noncomputable section

abbrev d004151 := Fin 3 → ℝ

def d004152 (i : Fin 3) : _root_.GD.N0232.N0720.N1292.d004151 →L[ℝ] ℝ := ContinuousLinearMap.proj i

def d004153 (p : _root_.GD.N0232.N0720.N1292.d004151) (t : _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  p 0 * (1 - (t : ℝ)) + p 1 * (t : ℝ) + p 2 * (t : ℝ) * (1 - (t : ℝ))

def d004154 (p : _root_.GD.N0232.N0720.N1292.d004151) : ℝ := min (p 0) (p 1) + min (p 2) 0

def d004155 : Set _root_.GD.N0232.N0720.N1292.d004151 := {p | 0 < _root_.GD.N0232.N0720.N1292.d004154 p}

theorem d004156 : Continuous _root_.GD.N0232.N0720.N1292.d004154 := by
  unfold _root_.GD.N0232.N0720.N1292.d004154
  fun_prop

theorem d004157 : IsOpen _root_.GD.N0232.N0720.N1292.d004155 :=
  isOpen_lt continuous_const _root_.GD.N0232.N0720.N1292.d004156

theorem d004158 (p : _root_.GD.N0232.N0720.N1292.d004151) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    _root_.GD.N0232.N0720.N1292.d004154 p ≤ _root_.GD.N0232.N0720.N1292.d004153 p t := by
  have hleft := mul_le_mul_of_nonneg_right (min_le_left (p 0) (p 1))
    (sub_nonneg.mpr t.2.2)
  have hright := mul_le_mul_of_nonneg_right (min_le_right (p 0) (p 1)) t.2.1
  have hV0 : 0 ≤ (t : ℝ) * (1 - (t : ℝ)) :=
    mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2)
  have hV1 : (t : ℝ) * (1 - (t : ℝ)) ≤ 1 := by nlinarith [t.2.1, t.2.2, sq_nonneg (t : ℝ)]
  have hcontrast : min (p 2) 0 ≤ p 2 * ((t : ℝ) * (1 - (t : ℝ))) := by
    by_cases hp : 0 ≤ p 2
    · rw [min_eq_right hp]
      exact mul_nonneg hp hV0
    · rw [min_eq_left (le_of_not_ge hp)]
      have h := mul_le_mul_of_nonpos_left hV1 (le_of_not_ge hp)
      simpa only [mul_one] using h
  unfold _root_.GD.N0232.N0720.N1292.d004154 _root_.GD.N0232.N0720.N1292.d004153
  nlinarith

theorem d004159 {p : _root_.GD.N0232.N0720.N1292.d004151} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    0 < _root_.GD.N0232.N0720.N1292.d004153 p t := hp.trans_le (_root_.GD.N0232.N0720.N1292.d004158 p t)

theorem d004160 {p : _root_.GD.N0232.N0720.N1292.d004151}
    (hz : 0 < p 0) (hw : 0 < p 1) (hu : 0 ≤ p 2) : p ∈ _root_.GD.N0232.N0720.N1292.d004155 := by
  change 0 < min (p 0) (p 1) + min (p 2) 0
  rw [min_eq_right hu, add_zero]
  exact lt_min hz hw

def d004161 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (p : _root_.GD.N0232.N0720.N1292.d004151) (t : _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  phi t * (_root_.GD.N0232.N0720.N1292.d004153 p t) ^ (-q)

def d004162 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (p : _root_.GD.N0232.N0720.N1292.d004151) : ℝ :=
  ∫ t, _root_.GD.N0232.N0720.N1292.d004161 q phi p t ∂mu

theorem d004163 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    {p : _root_.GD.N0232.N0720.N1292.d004151} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) : Continuous (_root_.GD.N0232.N0720.N1292.d004161 q phi p) := by
  unfold _root_.GD.N0232.N0720.N1292.d004161
  apply hphi.mul
  apply Continuous.rpow_const
  · unfold _root_.GD.N0232.N0720.N1292.d004153
    fun_prop
  · intro t
    exact Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1292.d004159 hp t))

theorem d004164 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] {p : _root_.GD.N0232.N0720.N1292.d004151} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) :
    Integrable (_root_.GD.N0232.N0720.N1292.d004161 q phi p) mu :=
  (_root_.GD.N0232.N0720.N1292.d004163 q hphi hp).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem d004165 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi) :
    ContinuousOn (fun pt : _root_.GD.N0232.N0720.N1292.d004151 × _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1292.d004161 q phi pt.1 pt.2)
      (_root_.GD.N0232.N0720.N1292.d004155 ×ˢ (univ : Set _root_.GD.N0232.N0720.N1290.d004131)) := by
  unfold _root_.GD.N0232.N0720.N1292.d004161
  apply (hphi.comp continuous_snd).continuousOn.mul
  apply ContinuousOn.rpow_const
  · unfold _root_.GD.N0232.N0720.N1292.d004153
    fun_prop
  · intro pt hpt
    exact Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1292.d004159 hpt.1 pt.2))

def d004166 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (p : _root_.GD.N0232.N0720.N1292.d004151) (t : _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1292.d004151 →L[ℝ] ℝ :=
  (-q * _root_.GD.N0232.N0720.N1292.d004161 (q + 1) (fun t ↦ phi t * (1 - (t : ℝ))) p t) • _root_.GD.N0232.N0720.N1292.d004152 0 +
  (-q * _root_.GD.N0232.N0720.N1292.d004161 (q + 1) (fun t ↦ phi t * (t : ℝ)) p t) • _root_.GD.N0232.N0720.N1292.d004152 1 +
  (-q * _root_.GD.N0232.N0720.N1292.d004161 (q + 1) (fun t ↦ phi t * ((t : ℝ) * (1 - (t : ℝ)))) p t) • _root_.GD.N0232.N0720.N1292.d004152 2

def d004167 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (p : _root_.GD.N0232.N0720.N1292.d004151) : _root_.GD.N0232.N0720.N1292.d004151 →L[ℝ] ℝ :=
  (-q * _root_.GD.N0232.N0720.N1292.d004162 (q + 1) (fun t ↦ phi t * (1 - (t : ℝ))) mu p) • _root_.GD.N0232.N0720.N1292.d004152 0 +
  (-q * _root_.GD.N0232.N0720.N1292.d004162 (q + 1) (fun t ↦ phi t * (t : ℝ)) mu p) • _root_.GD.N0232.N0720.N1292.d004152 1 +
  (-q * _root_.GD.N0232.N0720.N1292.d004162 (q + 1) (fun t ↦ phi t * ((t : ℝ) * (1 - (t : ℝ)))) mu p) • _root_.GD.N0232.N0720.N1292.d004152 2

theorem d004168 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    {p : _root_.GD.N0232.N0720.N1292.d004151} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    HasFDerivAt (fun s ↦ _root_.GD.N0232.N0720.N1292.d004161 q phi s t) (_root_.GD.N0232.N0720.N1292.d004166 q phi p t) p := by
  have hbase : HasFDerivAt (fun s : _root_.GD.N0232.N0720.N1292.d004151 ↦ _root_.GD.N0232.N0720.N1292.d004153 s t)
      ((1 - (t : ℝ)) • _root_.GD.N0232.N0720.N1292.d004152 0 + (t : ℝ) • _root_.GD.N0232.N0720.N1292.d004152 1 +
        ((t : ℝ) * (1 - (t : ℝ))) • _root_.GD.N0232.N0720.N1292.d004152 2) p := by
    let L : _root_.GD.N0232.N0720.N1292.d004151 →L[ℝ] ℝ :=
      (1 - (t : ℝ)) • _root_.GD.N0232.N0720.N1292.d004152 0 + (t : ℝ) • _root_.GD.N0232.N0720.N1292.d004152 1 +
        ((t : ℝ) * (1 - (t : ℝ))) • _root_.GD.N0232.N0720.N1292.d004152 2
    convert! L.hasFDerivAt (x := p) using 1
    funext s
    simp only [L, _root_.GD.N0232.N0720.N1292.d004153, _root_.GD.N0232.N0720.N1292.d004152, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  have hpow := hbase.rpow_const (p := -q) (Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1292.d004159 hp t)))
  convert! hpow.const_mul (phi t) using 1
  ext v
  simp only [_root_.GD.N0232.N0720.N1292.d004166, _root_.GD.N0232.N0720.N1292.d004161, _root_.GD.N0232.N0720.N1292.d004152, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [show -q - 1 = -(q + 1) by ring]
  ring

theorem d004169 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi) :
    ContinuousOn (fun pt : _root_.GD.N0232.N0720.N1292.d004151 × _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1292.d004166 q phi pt.1 pt.2)
      (_root_.GD.N0232.N0720.N1292.d004155 ×ˢ (univ : Set _root_.GD.N0232.N0720.N1290.d004131)) := by
  unfold _root_.GD.N0232.N0720.N1292.d004166
  exact ((((_root_.GD.N0232.N0720.N1292.d004165 (q + 1) (hphi.mul (by fun_prop))).const_mul _).smul
    continuousOn_const).add
    (((_root_.GD.N0232.N0720.N1292.d004165 (q + 1) (hphi.mul continuous_subtype_val)).const_mul _).smul
      continuousOn_const)).add
    (((_root_.GD.N0232.N0720.N1292.d004165 (q + 1) (hphi.mul (by fun_prop))).const_mul _).smul
      continuousOn_const)

theorem d004170 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    {p : _root_.GD.N0232.N0720.N1292.d004151} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) : Continuous (_root_.GD.N0232.N0720.N1292.d004166 q phi p) := by
  unfold _root_.GD.N0232.N0720.N1292.d004166
  exact ((((_root_.GD.N0232.N0720.N1292.d004163 (q + 1) (hphi.mul (by fun_prop)) hp).const_mul _).smul
    continuous_const).add
    (((_root_.GD.N0232.N0720.N1292.d004163 (q + 1) (hphi.mul continuous_subtype_val) hp).const_mul _).smul
      continuous_const)).add
    (((_root_.GD.N0232.N0720.N1292.d004163 (q + 1) (hphi.mul (by fun_prop)) hp).const_mul _).smul
      continuous_const)

theorem d004171 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] {p : _root_.GD.N0232.N0720.N1292.d004151} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) :
    (∫ t, _root_.GD.N0232.N0720.N1292.d004166 q phi p t ∂mu) = _root_.GD.N0232.N0720.N1292.d004167 q phi mu p := by
  have h0 := _root_.GD.N0232.N0720.N1292.d004164 (q + 1) (hphi.mul (by fun_prop)) mu hp
    (phi := fun t ↦ phi t * (1 - (t : ℝ)))
  have h1 := _root_.GD.N0232.N0720.N1292.d004164 (q + 1) (hphi.mul continuous_subtype_val) mu hp
    (phi := fun t ↦ phi t * (t : ℝ))
  have h2 := _root_.GD.N0232.N0720.N1292.d004164 (q + 1) (hphi.mul (by fun_prop)) mu hp
    (phi := fun t ↦ phi t * ((t : ℝ) * (1 - (t : ℝ))))
  unfold _root_.GD.N0232.N0720.N1292.d004166 _root_.GD.N0232.N0720.N1292.d004167
  rw [integral_add (((h0.const_mul _).smul_const _).add ((h1.const_mul _).smul_const _))
      ((h2.const_mul _).smul_const _),
    integral_add ((h0.const_mul _).smul_const _) ((h1.const_mul _).smul_const _),
    integral_smul_const, integral_smul_const, integral_smul_const,
    integral_const_mul, integral_const_mul, integral_const_mul]
  rfl



theorem d004172 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] {p : _root_.GD.N0232.N0720.N1292.d004151} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1292.d004162 q phi mu) (_root_.GD.N0232.N0720.N1292.d004167 q phi mu p) p := by
  obtain ⟨epsilon, he, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.1 (_root_.GD.N0232.N0720.N1292.d004157.mem_nhds hp)
  have hcont := (_root_.GD.N0232.N0720.N1292.d004169 q hphi).mono
    (Set.prod_mono hball (Subset.refl _))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p epsilon).prod isCompact_univ).exists_bound_of_continuousOn hcont
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := _root_.GD.N0232.N0720.N1292.d004161 q phi) (F' := _root_.GD.N0232.N0720.N1292.d004166 q phi) (μ := mu)
    (s := closedBall p epsilon) (bound := fun _ : _root_.GD.N0232.N0720.N1290.d004131 ↦ C)
    (closedBall_mem_nhds p he)
    (by
      filter_upwards [_root_.GD.N0232.N0720.N1292.d004157.mem_nhds hp] with s hs
      exact (_root_.GD.N0232.N0720.N1292.d004163 q hphi hs).aestronglyMeasurable)
    (_root_.GD.N0232.N0720.N1292.d004164 q hphi mu hp)
    (_root_.GD.N0232.N0720.N1292.d004170 q hphi hp).aestronglyMeasurable
    (ae_of_all mu fun t s hs ↦ hC (s, t) ⟨hs, mem_univ t⟩)
    (integrable_const C)
    (ae_of_all mu fun t s hs ↦ _root_.GD.N0232.N0720.N1292.d004168 q phi (hball hs) t)
  rw [_root_.GD.N0232.N0720.N1292.d004171 q hphi mu hp] at hderiv
  exact hderiv



theorem d004173 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1292.d004162 q phi mu) _root_.GD.N0232.N0720.N1292.d004155 := by
  have hall : ∀ n : ℕ, ∀ q : ℝ, ∀ phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ, Continuous phi →
      ContDiffOn ℝ n (_root_.GD.N0232.N0720.N1292.d004162 q phi mu) _root_.GD.N0232.N0720.N1292.d004155 := by
    intro n
    induction n with
    | zero =>
        intro q phi hphi
        change ContDiffOn ℝ 0 (_root_.GD.N0232.N0720.N1292.d004162 q phi mu) _root_.GD.N0232.N0720.N1292.d004155
        rw [contDiffOn_zero]
        intro p hp
        exact (_root_.GD.N0232.N0720.N1292.d004172 q hphi mu hp).continuousAt.continuousWithinAt
    | succ n ih =>
        intro q phi hphi
        rw [Nat.cast_add, Nat.cast_one]
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          _root_.GD.N0232.N0720.N1292.d004157.uniqueDiffOn).2
        refine ⟨by simp, _root_.GD.N0232.N0720.N1292.d004167 q phi mu, ?_, ?_⟩
        · unfold _root_.GD.N0232.N0720.N1292.d004167
          have h0 := ih (q + 1) (fun t ↦ phi t * (1 - (t : ℝ)))
            (hphi.mul (by fun_prop))
          have h1 := ih (q + 1) (fun t ↦ phi t * (t : ℝ))
            (hphi.mul continuous_subtype_val)
          have h2 := ih (q + 1) (fun t ↦ phi t * ((t : ℝ) * (1 - (t : ℝ))))
            (hphi.mul (by fun_prop))
          exact ((((contDiffOn_const (c := -q)).mul h0).smul contDiffOn_const).add
            (((contDiffOn_const (c := -q)).mul h1).smul contDiffOn_const)).add
              (((contDiffOn_const (c := -q)).mul h2).smul contDiffOn_const)
        · intro p hp
          exact (_root_.GD.N0232.N0720.N1292.d004172 q hphi mu hp).hasFDerivWithinAt
  exact contDiffOn_infty.mpr fun n ↦ hall n q phi hphi

end
end GD.N0232.N0720.N1292

#print axioms _root_.GD.N0232.N0720.N1292.d004172
#print axioms _root_.GD.N0232.N0720.N1292.d004173
