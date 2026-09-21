import GD.Module1754
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp












set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Filter Set
open scoped Topology

namespace GD.N0106.N0428.N0765.N1686
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1683

def d029102 : Set ℂ := {z | |z.im| < 1}

def d029103 (z : ℂ) : ℂ :=
  if z = Complex.I ∨ z = -Complex.I then 0 else _root_.GD.N0106.N0428.N0765.N1683.d029049 z

def d029104 (y : ℝ) : ℝ :=
  y ^ 2 - 32 * (3 * y ^ 2 + 1) / (1 - y ^ 2) ^ 3

theorem d029105 (z : ℂ) :
    z ^ 2 + 1 = (z - Complex.I) * (z + Complex.I) := by
  calc
    _ = z ^ 2 - Complex.I ^ 2 := by norm_num
    _ = _ := by ring

theorem d029106 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1686.d029102) :
    ¬ (z = Complex.I ∨ z = -Complex.I) := by
  rintro (rfl | rfl) <;> norm_num [_root_.GD.N0106.N0428.N0765.N1686.d029102] at hz

theorem d029107 {z : ℂ} (hz : z.re ≠ 0) :
    ¬ (z = Complex.I ∨ z = -Complex.I) := by
  rintro (rfl | rfl) <;> simp at hz

theorem d029108 {z : ℂ}
    (hz : ¬ (z = Complex.I ∨ z = -Complex.I)) : z ^ 2 + 1 ≠ 0 := by
  rw [_root_.GD.N0106.N0428.N0765.N1686.d029105]
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (fun h => hz (Or.inl h))
  · intro h
    apply hz
    right
    exact eq_neg_iff_add_eq_zero.mpr h

theorem d029109 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1686.d029102) :
    z ^ 2 + 1 ≠ 0 :=
  _root_.GD.N0106.N0428.N0765.N1686.d029108 (_root_.GD.N0106.N0428.N0765.N1686.d029106 hz)

theorem d029110 {z : ℂ} (hz : z ^ 2 + 1 ≠ 0) :
    DifferentiableAt ℂ _root_.GD.N0106.N0428.N0765.N1683.d029049 z := by
  have hn : DifferentiableAt ℂ (fun w : ℂ => 32 * (3 * w ^ 2 - 1)) z := by
    fun_prop
  have hd : DifferentiableAt ℂ (fun w : ℂ => w ^ 2 + 1) z := by fun_prop
  have hq := hn.div (hd.pow 3) (pow_ne_zero 3 hz)
  have he : DifferentiableAt ℂ _root_.GD.N0106.N0428.N0765.N1683.d029048 z := by
    exact ((differentiableAt_id.pow 2).neg).add hq
  exact he.cexp

theorem d029111 : DifferentiableOn ℂ _root_.GD.N0106.N0428.N0765.N1683.d029049 _root_.GD.N0106.N0428.N0765.N1686.d029102 := by
  intro z hz
  exact (_root_.GD.N0106.N0428.N0765.N1686.d029110 (_root_.GD.N0106.N0428.N0765.N1686.d029109 hz)).differentiableWithinAt


theorem d029112 (r : ℝ) (hr : r < 1) :
    ContinuousOn _root_.GD.N0106.N0428.N0765.N1683.d029049 {z : ℂ | |z.im| ≤ r} := by
  intro z hz
  exact (_root_.GD.N0106.N0428.N0765.N1686.d029110 (_root_.GD.N0106.N0428.N0765.N1686.d029109
    (lt_of_le_of_lt hz hr))).continuousAt.continuousWithinAt

theorem d029113 (y : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1683.d029048 ((y : ℂ) * Complex.I) = (_root_.GD.N0106.N0428.N0765.N1686.d029104 y : ℂ) := by
  have hsq : ((y : ℂ) * Complex.I) ^ 2 = -(y : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1683.d029048 _root_.GD.N0106.N0428.N0765.N1686.d029104
  rw [hsq]
  push_cast
  ring

theorem d029114 (y : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1683.d029049 ((y : ℂ) * Complex.I) = (Real.exp (_root_.GD.N0106.N0428.N0765.N1686.d029104 y) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1683.d029049, _root_.GD.N0106.N0428.N0765.N1686.d029113, ← Complex.ofReal_exp]

theorem d029115 {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - y ^ 2 := by
  have hp := mul_pos (sub_pos.mpr hy.1) (sub_pos.mpr hy.2)
  nlinarith



theorem d029116 (c : ℝ) (hc : c ^ 2 = 1) :
    Tendsto _root_.GD.N0106.N0428.N0765.N1686.d029104 (𝓝[Ioo (-1 : ℝ) 1] c) atBot := by
  let l : Filter ℝ := 𝓝[Ioo (-1 : ℝ) 1] c
  have hy : Tendsto (fun y : ℝ => y) l (𝓝 c) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun y : ℝ => y ^ 2) l (𝓝 (1 : ℝ)) := by
    simpa only [hc] using hy.pow 2
  have hzero : Tendsto (fun y : ℝ => (1 - y ^ 2) ^ 3) l (𝓝 (0 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsq).pow 3
  have hin : ∀ᶠ y in l, y ∈ Ioo (-1 : ℝ) 1 := self_mem_nhdsWithin
  have hden : Tendsto (fun y : ℝ => (1 - y ^ 2) ^ 3) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hzero, ?_⟩
    filter_upwards [hin] with y hy
    exact pow_pos (_root_.GD.N0106.N0428.N0765.N1686.d029115 hy) 3
  have hinv : Tendsto (fun y : ℝ => ((1 - y ^ 2) ^ 3)⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  apply tendsto_atBot.2
  intro M
  filter_upwards [hinv.eventually (eventually_ge_atTop ((1 - M) / 32)), hin] with y hi hy
  have hd : 0 < (1 - y ^ 2) ^ 3 := pow_pos (_root_.GD.N0106.N0428.N0765.N1686.d029115 hy) 3
  have hs : y ^ 2 ≤ 1 := le_of_lt (by linarith [_root_.GD.N0106.N0428.N0765.N1686.d029115 hy])
  have hnum : (32 : ℝ) / (1 - y ^ 2) ^ 3 ≤
      32 * (3 * y ^ 2 + 1) / (1 - y ^ 2) ^ 3 :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg y]) hd.le
  change _root_.GD.N0106.N0428.N0765.N1686.d029104 y ≤ M
  unfold _root_.GD.N0106.N0428.N0765.N1686.d029104
  rw [div_eq_mul_inv] at hnum
  linarith only [hi, hs, hnum]

theorem d029117 (c : ℝ) (hc : c ^ 2 = 1) :
    Tendsto (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1683.d029049 ((y : ℂ) * Complex.I))
      (𝓝[Ioo (-1 : ℝ) 1] c) (𝓝 (0 : ℂ)) := by
  have hreal := Real.tendsto_exp_atBot.comp (_root_.GD.N0106.N0428.N0765.N1686.d029116 c hc)
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  simpa only [_root_.GD.N0106.N0428.N0765.N1686.d029114, Complex.ofReal_zero, Function.comp_def] using hcomplex

theorem d029118 {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    ContinuousAt (fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (t : ℂ) * Complex.I)) y := by
  have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re ≠ 0 := by simpa using hx
  have hf := (_root_.GD.N0106.N0428.N0765.N1686.d029110
    (_root_.GD.N0106.N0428.N0765.N1686.d029108 (_root_.GD.N0106.N0428.N0765.N1686.d029107 hre))).continuousAt
  have hg : ContinuousAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) y := by
    fun_prop
  exact ContinuousAt.comp (f := fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) hf hg


theorem d029119 (x : ℝ) :
    Tendsto (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[Ioo (-1 : ℝ) 1] (1 : ℝ)) (𝓝 (_root_.GD.N0106.N0428.N0765.N1683.d029052 x)) := by
  by_cases hx : x = 0
  · subst x
    simpa [_root_.GD.N0106.N0428.N0765.N1683.d029052] using _root_.GD.N0106.N0428.N0765.N1686.d029117 1 (by norm_num)
  · simpa [_root_.GD.N0106.N0428.N0765.N1683.d029052, hx] using
      (_root_.GD.N0106.N0428.N0765.N1686.d029118 hx 1).tendsto.mono_left nhdsWithin_le_nhds


theorem d029120 (x : ℝ) :
    Tendsto (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[Ioo (-1 : ℝ) 1] (-1 : ℝ)) (𝓝 (_root_.GD.N0106.N0428.N0765.N1683.d029053 x)) := by
  by_cases hx : x = 0
  · subst x
    simpa [_root_.GD.N0106.N0428.N0765.N1683.d029053] using _root_.GD.N0106.N0428.N0765.N1686.d029117 (-1) (by norm_num)
  · simpa [_root_.GD.N0106.N0428.N0765.N1683.d029053, hx, sub_eq_add_neg] using
      (_root_.GD.N0106.N0428.N0765.N1686.d029118 hx (-1)).tendsto.mono_left nhdsWithin_le_nhds

theorem d029121 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1686.d029102) : _root_.GD.N0106.N0428.N0765.N1686.d029103 z = _root_.GD.N0106.N0428.N0765.N1683.d029049 z := by
  rw [_root_.GD.N0106.N0428.N0765.N1686.d029103, if_neg (_root_.GD.N0106.N0428.N0765.N1686.d029106 hz)]

theorem d029122 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1686.d029103 (x : ℂ) = (_root_.GD.N0106.N0428.N0765.N1683.d029050 x : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1686.d029121 (by simp [_root_.GD.N0106.N0428.N0765.N1686.d029102]), _root_.GD.N0106.N0428.N0765.N1683.d029056]

theorem d029123 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) + Complex.I) = _root_.GD.N0106.N0428.N0765.N1683.d029052 x := by
  by_cases hx : x = 0
  · simp [_root_.GD.N0106.N0428.N0765.N1686.d029103, _root_.GD.N0106.N0428.N0765.N1683.d029052, hx]
  · have hre : ((x : ℂ) + Complex.I).re ≠ 0 := by simpa using hx
    rw [_root_.GD.N0106.N0428.N0765.N1686.d029103, if_neg (_root_.GD.N0106.N0428.N0765.N1686.d029107 hre), _root_.GD.N0106.N0428.N0765.N1683.d029052, if_neg hx]

theorem d029124 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) - Complex.I) = _root_.GD.N0106.N0428.N0765.N1683.d029053 x := by
  by_cases hx : x = 0
  · simp [_root_.GD.N0106.N0428.N0765.N1686.d029103, _root_.GD.N0106.N0428.N0765.N1683.d029053, hx]
  · have hre : ((x : ℂ) - Complex.I).re ≠ 0 := by simpa using hx
    rw [_root_.GD.N0106.N0428.N0765.N1686.d029103, if_neg (_root_.GD.N0106.N0428.N0765.N1686.d029107 hre), _root_.GD.N0106.N0428.N0765.N1683.d029053, if_neg hx]

theorem d029125 : DifferentiableOn ℂ _root_.GD.N0106.N0428.N0765.N1686.d029103 _root_.GD.N0106.N0428.N0765.N1686.d029102 :=
  _root_.GD.N0106.N0428.N0765.N1686.d029111.congr (fun _ hz => _root_.GD.N0106.N0428.N0765.N1686.d029121 hz)

theorem d029126 (r : ℝ) (hr : r < 1) :
    ContinuousOn _root_.GD.N0106.N0428.N0765.N1686.d029103 {z : ℂ | |z.im| ≤ r} :=
  (_root_.GD.N0106.N0428.N0765.N1686.d029112 r hr).congr
    (fun _ hz => _root_.GD.N0106.N0428.N0765.N1686.d029121 (lt_of_le_of_lt hz hr))

theorem d029127 (x : ℝ) :
    Tendsto (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[Ioo (-1 : ℝ) 1] (1 : ℝ)) (𝓝 (_root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) + Complex.I))) := by
  rw [_root_.GD.N0106.N0428.N0765.N1686.d029123]
  apply (_root_.GD.N0106.N0428.N0765.N1686.d029119 x).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (_root_.GD.N0106.N0428.N0765.N1686.d029121 (by simpa [_root_.GD.N0106.N0428.N0765.N1686.d029102, abs_lt] using hy)).symm

theorem d029128 (x : ℝ) :
    Tendsto (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[Ioo (-1 : ℝ) 1] (-1 : ℝ)) (𝓝 (_root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) - Complex.I))) := by
  rw [_root_.GD.N0106.N0428.N0765.N1686.d029124]
  apply (_root_.GD.N0106.N0428.N0765.N1686.d029120 x).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (_root_.GD.N0106.N0428.N0765.N1686.d029121 (by simpa [_root_.GD.N0106.N0428.N0765.N1686.d029102, abs_lt] using hy)).symm

end
end GD.N0106.N0428.N0765.N1686

#print axioms _root_.GD.N0106.N0428.N0765.N1686.d029111
#print axioms _root_.GD.N0106.N0428.N0765.N1686.d029116
#print axioms _root_.GD.N0106.N0428.N0765.N1686.d029119
#print axioms _root_.GD.N0106.N0428.N0765.N1686.d029120
#print axioms _root_.GD.N0106.N0428.N0765.N1686.d029127
#print axioms _root_.GD.N0106.N0428.N0765.N1686.d029128
