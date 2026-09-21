import GD.Module0015




























open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace GD
namespace N0230
namespace N0640

noncomputable section

open _root_.GD.N0230.N0602


def d000252 (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹


def d000253 (a : ℝ) (n : ℕ) : ℝ :=
  a / (a + _root_.GD.N0230.N0640.d000252 n)


def d000254 (a : ℝ) : ℕ → ℝ
  | 0 => _root_.GD.N0230.N0640.d000253 a 0
  | n + 1 => _root_.GD.N0230.N0640.d000253 a (n + 1) - _root_.GD.N0230.N0640.d000253 a n


def d000255 (a : ℝ) (n : ℕ) : ℝ :=
  1 - _root_.GD.N0230.N0640.d000253 a n

theorem d000256 (n : ℕ) : 0 < _root_.GD.N0230.N0640.d000252 n := by
  unfold _root_.GD.N0230.N0640.d000252
  positivity

theorem d000257 (n : ℕ) :
    _root_.GD.N0230.N0640.d000252 (n + 1) = _root_.GD.N0230.N0640.d000252 n / 2 := by
  unfold _root_.GD.N0230.N0640.d000252
  rw [pow_succ]
  field_simp

theorem d000258 (n : ℕ) :
    _root_.GD.N0230.N0640.d000252 (n + 1) ≤ _root_.GD.N0230.N0640.d000252 n := by
  rw [_root_.GD.N0230.N0640.d000257]
  exact div_le_self (_root_.GD.N0230.N0640.d000256 n).le (by norm_num)

theorem d000259 {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ _root_.GD.N0230.N0640.d000253 a n := by
  unfold _root_.GD.N0230.N0640.d000253
  exact div_nonneg ha (add_nonneg ha (_root_.GD.N0230.N0640.d000256 n).le)

theorem d000260 {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    _root_.GD.N0230.N0640.d000253 a n ≤ 1 := by
  unfold _root_.GD.N0230.N0640.d000253
  apply (div_le_one (add_pos_of_nonneg_of_pos ha (_root_.GD.N0230.N0640.d000256 n))).2
  exact le_add_of_nonneg_right (_root_.GD.N0230.N0640.d000256 n).le


theorem d000261 {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    _root_.GD.N0230.N0640.d000255 a n =
      _root_.GD.N0230.N0640.d000252 n / (a + _root_.GD.N0230.N0640.d000252 n) := by
  unfold _root_.GD.N0230.N0640.d000255 _root_.GD.N0230.N0640.d000253
  have hden : a + _root_.GD.N0230.N0640.d000252 n ≠ 0 :=
    (add_pos_of_nonneg_of_pos ha (_root_.GD.N0230.N0640.d000256 n)).ne'
  field_simp
  ring

theorem d000262 {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ _root_.GD.N0230.N0640.d000255 a n := by
  unfold _root_.GD.N0230.N0640.d000255
  linarith [_root_.GD.N0230.N0640.d000260 ha n]

theorem d000263 (a : ℝ) (n : ℕ) :
    _root_.GD.N0230.N0640.d000253 a n + _root_.GD.N0230.N0640.d000255 a n = 1 := by
  simp [_root_.GD.N0230.N0640.d000255]

theorem d000264 {a : ℝ} (ha : 0 ≤ a) :
    Monotone (_root_.GD.N0230.N0640.d000253 a) := by
  intro m n hmn
  unfold _root_.GD.N0230.N0640.d000253
  have ht : _root_.GD.N0230.N0640.d000252 n ≤ _root_.GD.N0230.N0640.d000252 m := by
    exact (antitone_nat_of_succ_le _root_.GD.N0230.N0640.d000258) hmn
  have hdm : 0 < a + _root_.GD.N0230.N0640.d000252 m :=
    add_pos_of_nonneg_of_pos ha (_root_.GD.N0230.N0640.d000256 m)
  have hdn : 0 < a + _root_.GD.N0230.N0640.d000252 n :=
    add_pos_of_nonneg_of_pos ha (_root_.GD.N0230.N0640.d000256 n)
  exact (div_le_div_iff₀ hdm hdn).2 (by nlinarith)

theorem d000265 {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ _root_.GD.N0230.N0640.d000254 a n := by
  cases n with
  | zero =>
      simpa [_root_.GD.N0230.N0640.d000254] using _root_.GD.N0230.N0640.d000259 ha 0
  | succ n =>
      simpa [_root_.GD.N0230.N0640.d000254] using
        (_root_.GD.N0230.N0640.d000264 ha (Nat.le_succ n))


theorem d000266 (a : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), _root_.GD.N0230.N0640.d000254 a j) =
      _root_.GD.N0230.N0640.d000253 a n := by
  induction n with
  | zero => simp [_root_.GD.N0230.N0640.d000254]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [_root_.GD.N0230.N0640.d000254]


theorem d000267 {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    _root_.GD.N0230.N0640.d000253 a n ≤ (2 : ℝ) ^ n * a := by
  unfold _root_.GD.N0230.N0640.d000253 _root_.GD.N0230.N0640.d000252
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have ht : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hp
  have hd : 0 < a + ((2 : ℝ) ^ n)⁻¹ :=
    add_pos_of_nonneg_of_pos ha ht
  apply (div_le_iff₀ hd).2
  have hcancel : (2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹ = 1 := by
    exact mul_inv_cancel₀ hp.ne'
  nlinarith [mul_nonneg hp.le ha]

theorem d000268 :
    Tendsto _root_.GD.N0230.N0640.d000252 atTop (nhds 0) := by
  unfold _root_.GD.N0230.N0640.d000252
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))



theorem d000269 {a : ℝ} (ha : 0 < a) :
    Tendsto (_root_.GD.N0230.N0640.d000253 a) atTop (nhds 1) := by
  unfold _root_.GD.N0230.N0640.d000253
  have hden : Tendsto (fun n : ℕ => a + _root_.GD.N0230.N0640.d000252 n)
      atTop (nhds a) := by
    simpa using tendsto_const_nhds.add _root_.GD.N0230.N0640.d000268
  have hdiv : Tendsto (fun n : ℕ => a / (a + _root_.GD.N0230.N0640.d000252 n))
      atTop (nhds (a / a)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (nhds a)).div
      hden ha.ne'
  simpa [ha.ne'] using hdiv


def d000270 {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (density : Ω → ℝ)
    (h : _root_.GD.N0230.N0602.d000116 base) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal
    (_root_.GD.N0230.N0640.d000253 (density ω) n * h ω ^ 2) ∂base


def d000271 {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (h : _root_.GD.N0230.N0602.d000116 base) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (h ω ^ 2) ∂base




def d000272 {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (density : Ω → ℝ)
    (h : _root_.GD.N0230.N0602.d000116 base) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (density ω * h ω ^ 2) ∂base

theorem d000273
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (density : Ω → ℝ)
    (h : _root_.GD.N0230.N0602.d000116 base) (n : ℕ) :
    0 ≤ _root_.GD.N0230.N0640.d000270 base density h n :=
  bot_le



theorem d000274
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (density : Ω → ℝ)
    (hdensity_measurable : Measurable density)
    (hdensity_nonneg : ∀ ω, 0 ≤ density ω)
    (h : _root_.GD.N0230.N0602.d000116 base) (n : ℕ) :
    _root_.GD.N0230.N0640.d000270 base density h n ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) *
        _root_.GD.N0230.N0640.d000272 base density h := by
  unfold _root_.GD.N0230.N0640.d000270 _root_.GD.N0230.N0640.d000272
  calc
    (∫⁻ ω, ENNReal.ofReal
        (_root_.GD.N0230.N0640.d000253 (density ω) n * h ω ^ 2) ∂base) ≤
        ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) ^ n) *
          ENNReal.ofReal (density ω * h ω ^ 2) ∂base := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal
          (_root_.GD.N0230.N0640.d000253 (density ω) n * h ω ^ 2) ≤
        ENNReal.ofReal ((2 : ℝ) ^ n) *
          ENNReal.ofReal (density ω * h ω ^ 2)
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ n)]
      apply ENNReal.ofReal_le_ofReal
      have hsquare : 0 ≤ h ω ^ 2 := sq_nonneg _
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        (_root_.GD.N0230.N0640.d000267 (hdensity_nonneg ω) n) hsquare
    _ = ENNReal.ofReal ((2 : ℝ) ^ n) *
        ∫⁻ ω, ENNReal.ofReal (density ω * h ω ^ 2) ∂base := by
      rw [lintegral_const_mul'' _]
      exact ((hdensity_measurable.aemeasurable.mul
        ((Lp.aestronglyMeasurable h).aemeasurable.pow_const 2)).ennreal_ofReal)





theorem d000275
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (density : Ω → ℝ)
    (hdensity_measurable : Measurable density)
    (hdensity_pos : ∀ᵐ ω ∂base, 0 < density ω)
    (h : _root_.GD.N0230.N0602.d000116 base) :
    Tendsto (fun n => _root_.GD.N0230.N0640.d000270 base density h n)
      atTop (nhds (_root_.GD.N0230.N0640.d000271 base h)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    have hhead : Measurable (fun ω => _root_.GD.N0230.N0640.d000253 (density ω) n) := by
      unfold _root_.GD.N0230.N0640.d000253
      fun_prop
    exact ((hhead.aemeasurable.mul
      ((Lp.aestronglyMeasurable h).aemeasurable.pow_const 2)).ennreal_ofReal)
  · filter_upwards [hdensity_pos] with ω hpos
    intro m n hmn
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (_root_.GD.N0230.N0640.d000264 hpos.le hmn) (sq_nonneg _)
  · filter_upwards [hdensity_pos] with ω hpos
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    simpa using (_root_.GD.N0230.N0640.d000269 hpos).mul_const (h ω ^ 2)




theorem d000276
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (densitySeq : ℕ → Ω → ℝ)
    (hdensity_measurable : ∀ j, Measurable (densitySeq j))
    (hdensity_nonneg : ∀ j ω, 0 ≤ densitySeq j ω)
    (h : _root_.GD.N0230.N0602.d000116 base) (headLevel : ℕ)
    (htax : Tendsto
      (fun j => _root_.GD.N0230.N0640.d000272 base (densitySeq j) h)
      atTop (nhds 0)) :
    Tendsto
      (fun j => _root_.GD.N0230.N0640.d000270 base (densitySeq j) h headLevel)
      atTop (nhds 0) := by
  have hscaled : Tendsto
      (fun j => ENNReal.ofReal ((2 : ℝ) ^ headLevel) *
        _root_.GD.N0230.N0640.d000272 base (densitySeq j) h)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul htax
        (Or.inr ENNReal.ofReal_ne_top))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro b hb
    filter_upwards [(tendsto_order.1 hscaled).2 b hb] with j hj
    exact (_root_.GD.N0230.N0640.d000274
      base (densitySeq j) (hdensity_measurable j)
        (hdensity_nonneg j) h headLevel).trans_lt hj




theorem d000277
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (density : Ω → ℝ)
    (hdensity_measurable : Measurable density)
    (hdensity_pos : ∀ᵐ ω ∂base, 0 < density ω)
    (h : _root_.GD.N0230.N0602.d000116 base)
    (hzero : ∀ n, _root_.GD.N0230.N0640.d000270 base density h n = 0) :
    _root_.GD.N0230.N0640.d000271 base h = 0 := by
  have hrecover := _root_.GD.N0230.N0640.d000275
    base density hdensity_measurable hdensity_pos h
  have hvanish : Tendsto
      (fun n => _root_.GD.N0230.N0640.d000270 base density h n)
      atTop (nhds 0) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))
  exact tendsto_nhds_unique hrecover hvanish

end

end N0640
end N0230
end GD

#print axioms _root_.GD.N0230.N0640.d000266
#print axioms _root_.GD.N0230.N0640.d000267
#print axioms _root_.GD.N0230.N0640.d000269
#print axioms _root_.GD.N0230.N0640.d000274
#print axioms _root_.GD.N0230.N0640.d000275
#print axioms _root_.GD.N0230.N0640.d000276
#print axioms _root_.GD.N0230.N0640.d000277
