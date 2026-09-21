import GD.Module0545
import GD.Module0547
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0219
noncomputable section
open _root_.GD.N0208.N0455
open _root_.GD.N0218

def d008141 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume


def d008142 (s : ℝ) : ℝ := 2 * Real.sigmoid s ^ 2

theorem d008143 (s : ℝ) :
    _root_.GD.N0219.d008142 s = 2 * Real.exp (2 * s) / (1 + Real.exp s) ^ 2 := by
  have he : Real.exp (2 * s) = Real.exp s ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [he, _root_.GD.N0219.d008142, Real.sigmoid_def, Real.exp_neg]
  have hp := Real.exp_pos s
  field_simp
  ring

theorem d008144 (s : ℝ) :
    0 < _root_.GD.N0219.d008142 s ∧ _root_.GD.N0219.d008142 s ≤ 2 := by
  have hp := Real.sigmoid_pos s
  have hu := Real.sigmoid_le_one s
  unfold _root_.GD.N0219.d008142
  constructor
  · positivity
  · nlinarith

def d008145 (K N : ℝ) (z : ℝ × ℝ) : ℝ :=
  _root_.GD.N0219.d008142 z.1 * _root_.GD.N0208.N0455.d007937 K z.1 ^ 2 * _root_.GD.N0208.N0455.d007937 N z.2 ^ 2

@[fun_prop] theorem d008146 (K N : ℝ) :
    Measurable (_root_.GD.N0219.d008145 K N) := by
  unfold _root_.GD.N0219.d008145 _root_.GD.N0219.d008142
  exact (measurable_const.mul ((continuous_sigmoid.measurable.comp measurable_fst).pow_const 2)
    |>.mul (((_root_.GD.N0208.N0455.d007938 K).comp measurable_fst).pow_const 2)).mul
      (((_root_.GD.N0208.N0455.d007938 N).comp measurable_snd).pow_const 2)

theorem d008147 (K N : ℝ) (z : ℝ × ℝ) :
    0 ≤ _root_.GD.N0219.d008145 K N z ∧ _root_.GD.N0219.d008145 K N z ≤ 2 := by
  have hρ := _root_.GD.N0219.d008144 z.1
  have hK := _root_.GD.N0218.d008119 K z.1
  have hN := _root_.GD.N0218.d008119 N z.2
  have hsK : _root_.GD.N0208.N0455.d007937 K z.1 ^ 2 ≤ 1 := by nlinarith
  have hsN : _root_.GD.N0208.N0455.d007937 N z.2 ^ 2 ≤ 1 := by nlinarith
  refine ⟨mul_nonneg (mul_nonneg hρ.1.le (sq_nonneg _)) (sq_nonneg _), ?_⟩
  calc
    _ ≤ 2 * 1 * 1 := mul_le_mul
      (mul_le_mul hρ.2 hsK (sq_nonneg _) (by norm_num)) hsN
      (sq_nonneg _) (by norm_num)
    _ = 2 := by norm_num

def d008148 (K N : ℝ) : Set (ℝ × ℝ) :=
  Icc (-2 * K) (2 * K) ×ˢ Icc (-2 * N) (2 * N)

theorem d008149 (K N : ℝ) (hK : 0 < K) (hN : 0 < N)
    (z : ℝ × ℝ) (hz : z ∉ _root_.GD.N0219.d008148 K N) : _root_.GD.N0219.d008145 K N z = 0 := by
  have hrect : z ∈ _root_.GD.N0219.d008148 K N ↔ |z.1| ≤ 2*K ∧ |z.2| ≤ 2*N := by
    simp only [_root_.GD.N0219.d008148, mem_prod, mem_Icc, abs_le, neg_mul]
  by_cases hx : |z.1| ≤ 2*K
  · have hy : 2*N ≤ |z.2| := le_of_lt (lt_of_not_ge (fun hy => hz (hrect.mpr ⟨hx, hy⟩)))
    rw [_root_.GD.N0219.d008145, (_root_.GD.N0208.N0455.d007939 hN).2.2.2 z.2 hy]
    ring
  · have hx' : 2*K ≤ |z.1| := le_of_lt (lt_of_not_ge hx)
    rw [_root_.GD.N0219.d008145, (_root_.GD.N0208.N0455.d007939 hK).2.2.2 z.1 hx']
    ring

def d008150 (K N : ℝ) : Measure (ℝ × ℝ) :=
  _root_.GD.N0219.d008141.withDensity (fun z => ENNReal.ofReal (_root_.GD.N0219.d008145 K N z))

theorem d008151 (K N : ℝ) (hK : 0 < K) (hN : 0 < N) :
    _root_.GD.N0219.d008150 K N univ ≤ ENNReal.ofReal (32 * K * N) := by
  rw [_root_.GD.N0219.d008150, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ z : ℝ × ℝ, (_root_.GD.N0219.d008148 K N).indicator (fun _ => (2 : ℝ≥0∞)) z
        ∂_root_.GD.N0219.d008141 := by
      apply lintegral_mono
      intro z
      dsimp only
      by_cases hz : z ∈ _root_.GD.N0219.d008148 K N
      · rw [indicator_of_mem hz]
        exact (ENNReal.ofReal_le_ofReal (_root_.GD.N0219.d008147 K N z).2).trans_eq
          (by norm_num)
      · rw [indicator_of_notMem hz, _root_.GD.N0219.d008149 K N hK hN z hz]
        simp
    _ = 2 * (ENNReal.ofReal (4 * K) * ENNReal.ofReal (4 * N)) := by
      rw [lintegral_indicator_const (s := _root_.GD.N0219.d008148 K N)
        (measurableSet_Icc.prod measurableSet_Icc)]
      simp only [_root_.GD.N0219.d008141, _root_.GD.N0219.d008148, Measure.prod_prod, Real.volume_Icc]
      congr 2 <;> congr 1 <;> ring
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4*K),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem d008152 (K N : ℝ) (hK : 0 < K) (hN : 0 < N) :
    IsFiniteMeasure (_root_.GD.N0219.d008150 K N) :=
  ⟨(_root_.GD.N0219.d008151 K N hK hN).trans_lt ENNReal.ofReal_lt_top⟩

def d008153 : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
def d008154 : ℝ := _root_.GD.N0219.d008142 (-1)
def d008155 : Measure (ℝ × ℝ) :=
  _root_.GD.N0219.d008141.withDensity (_root_.GD.N0219.d008153.indicator (fun _ => ENNReal.ofReal _root_.GD.N0219.d008154))

theorem d008156 : _root_.GD.N0219.d008155 univ = ENNReal.ofReal _root_.GD.N0219.d008154 * 4 := by
  rw [_root_.GD.N0219.d008155, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_indicator_const (s := _root_.GD.N0219.d008153) (measurableSet_Icc.prod measurableSet_Icc)]
  simp only [_root_.GD.N0219.d008141, _root_.GD.N0219.d008153, Measure.prod_prod, Real.volume_Icc]
  norm_num

theorem d008157 : 0 < _root_.GD.N0219.d008155 univ := by
  rw [_root_.GD.N0219.d008156]
  exact ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.ofReal_pos.mpr (_root_.GD.N0219.d008144 (-1)).1, by norm_num⟩

instance d008158 : NeZero _root_.GD.N0219.d008155 := ⟨by
  intro h
  have hp := _root_.GD.N0219.d008157
  simp only [h, Measure.coe_zero, Pi.zero_apply, lt_self_iff_false] at hp⟩

theorem d008159 (K N : ℝ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
    _root_.GD.N0219.d008155 ≤ _root_.GD.N0219.d008150 K N := by
  apply withDensity_mono
  apply ae_of_all
  intro z
  dsimp only
  by_cases hz : z ∈ _root_.GD.N0219.d008153
  · rw [indicator_of_mem hz]
    have hzx : |z.1| ≤ 1 := abs_le.mpr hz.1
    have hzy : |z.2| ≤ 1 := abs_le.mpr hz.2
    rw [_root_.GD.N0219.d008145, (_root_.GD.N0208.N0455.d007939 (by linarith : 0 < K)).2.2.1 z.1
      (hzx.trans hK), (_root_.GD.N0208.N0455.d007939 (by linarith : 0 < N)).2.2.1 z.2 (hzy.trans hN)]
    simp only [one_pow, mul_one]
    apply ENNReal.ofReal_le_ofReal
    have hsig := Real.sigmoid_le hz.1.1
    have hs := mul_self_le_mul_self (Real.sigmoid_pos (-1)).le hsig
    simpa only [_root_.GD.N0219.d008154, _root_.GD.N0219.d008142, pow_two] using
      mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
  · rw [indicator_of_notMem hz]
    exact zero_le


theorem d008160 (K N : ℝ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
    0 < _root_.GD.N0219.d008150 K N univ ∧ _root_.GD.N0219.d008150 K N univ < ⊤ := by
  refine ⟨_root_.GD.N0219.d008157.trans_le (Measure.le_iff.mp (_root_.GD.N0219.d008159 K N hK hN)
    univ MeasurableSet.univ), ?_⟩
  exact (_root_.GD.N0219.d008151 K N (by linarith) (by linarith)).trans_lt ENNReal.ofReal_lt_top

def d008161 (N : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
    ENNReal.ofReal (_root_.GD.N0218.d008109 s / (2 * Real.pi * Real.cosh ((v + w) / 2))) *
      ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N s * _root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N s * _root_.GD.N0208.N0455.d007937 N w) ^ 2)

theorem d008162 : Tendsto _root_.GD.N0219.d008161 atTop (𝓝 0) :=
  _root_.GD.N0218.d008128 id



theorem d008163
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : AEMeasurable g _root_.GD.N0219.d008155)
    (hbound : ∀ᶠ N : ℝ in atTop, (∫⁻ z, g z ∂_root_.GD.N0219.d008150 N N) ≤ _root_.GD.N0219.d008161 N) :
    g =ᵐ[_root_.GD.N0219.d008155] 0 := by
  apply _root_.GD.N0222.d008137
    atTop _root_.GD.N0219.d008155 (fun N : ℝ => _root_.GD.N0219.d008150 N N) g hg _root_.GD.N0219.d008161 _ hbound
    _root_.GD.N0219.d008162
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  exact _root_.GD.N0219.d008159 N N hN hN

theorem d008164
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : AEMeasurable g _root_.GD.N0219.d008155)
    (hpositive : ∀ᵐ z ∂_root_.GD.N0219.d008155, 0 < g z)
    (hbound : ∀ᶠ N : ℝ in atTop, (∫⁻ z, g z ∂_root_.GD.N0219.d008150 N N) ≤ _root_.GD.N0219.d008161 N) :
    False := by
  have hz := _root_.GD.N0219.d008163 g hg hbound
  have hf : ∀ᵐ z ∂_root_.GD.N0219.d008155, False := by
    filter_upwards [hz, hpositive] with z hz hp
    exact hp.ne' hz
  exact (Eventually.exists hf).elim (fun _ h => h)

end
end GD.N0219

#print axioms _root_.GD.N0219.d008143
#print axioms _root_.GD.N0219.d008149
#print axioms _root_.GD.N0219.d008151
#print axioms _root_.GD.N0219.d008152
#print axioms _root_.GD.N0219.d008156
#print axioms _root_.GD.N0219.d008157
#print axioms _root_.GD.N0219.d008159
#print axioms _root_.GD.N0219.d008160
#print axioms _root_.GD.N0219.d008162
#print axioms _root_.GD.N0219.d008163
#print axioms _root_.GD.N0219.d008164
