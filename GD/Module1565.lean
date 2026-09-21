import GD.Module1560
import GD.Module0217
import GD.Module0895













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1725
noncomputable section

open _root_.GD.N0232.N0720.N1437

def d024116 : ℝ := 1 / 100000
def d024117 : ℝ := 1 / 250
def d024118 : ℝ := 1 / 10 ^ 12
def d024119 : ℝ := 1 / 10000

theorem d024120 : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024116 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024116]
theorem d024121 : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024118 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]
theorem d024122 : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024117 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024117]
theorem d024123 : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024119 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024119]


def d024124 (c w x : ℝ) : ℝ := max (1 - |x - c| / w) 0

def d024125 (c f w : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1725.d024124 c w p.1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f w p.2

def d024126 (c f w : ℝ) (p : ℝ × ℝ) : ℝ :=
  (_root_.GD.N0106.N0428.N0770.N1725.d024124 c w p.1 - _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 - c) w p.1) * _root_.GD.N0106.N0428.N0770.N1725.d024124 f w p.2

def d024127 : Fin 4 → ℝ := ![1 / 20, 3 / 20, 1 / 50, 1 / 10]
def d024128 : Fin 4 → ℝ := ![2, 1 / 50, 1 / 50, 1 / 50]
def d024129 : Fin 4 → ℝ :=
  ![-46233 / 500000, 294569 / 500000, 131993 / 1000000, 70711 / 1000000]


def d024130 (p : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 4, _root_.GD.N0106.N0428.N0770.N1725.d024129 i * _root_.GD.N0106.N0428.N0770.N1725.d024126 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i) (_root_.GD.N0106.N0428.N0770.N1725.d024128 i) _root_.GD.N0106.N0428.N0770.N1725.d024116 p


def d024131 (p : ℝ × ℝ) : ℝ :=
  3 * _root_.GD.N0106.N0428.N0770.N1725.d024126 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p -
    4 * _root_.GD.N0106.N0428.N0770.N1725.d024126 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p

theorem d024132 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024130 p = (-46233 / 500000) * _root_.GD.N0106.N0428.N0770.N1725.d024126 (1 / 20) 2 _root_.GD.N0106.N0428.N0770.N1725.d024116 p +
      (294569 / 500000) * _root_.GD.N0106.N0428.N0770.N1725.d024126 (3 / 20) (1 / 50) _root_.GD.N0106.N0428.N0770.N1725.d024116 p +
      (131993 / 1000000) * _root_.GD.N0106.N0428.N0770.N1725.d024126 (1 / 50) (1 / 50) _root_.GD.N0106.N0428.N0770.N1725.d024116 p +
      (70711 / 1000000) * _root_.GD.N0106.N0428.N0770.N1725.d024126 (1 / 10) (1 / 50) _root_.GD.N0106.N0428.N0770.N1725.d024116 p := by
  simp [_root_.GD.N0106.N0428.N0770.N1725.d024130, _root_.GD.N0106.N0428.N0770.N1725.d024129, _root_.GD.N0106.N0428.N0770.N1725.d024127, _root_.GD.N0106.N0428.N0770.N1725.d024128, Fin.sum_univ_succ]
  <;> ring

theorem d024133 (c w : ℝ) : Continuous (_root_.GD.N0106.N0428.N0770.N1725.d024124 c w) := by
  exact (continuous_const.sub
    ((continuous_id.sub continuous_const).abs.div_const w)).max continuous_const

theorem d024134 (c f w : ℝ) : Continuous (_root_.GD.N0106.N0428.N0770.N1725.d024126 c f w) :=
  (((_root_.GD.N0106.N0428.N0770.N1725.d024133 c w).comp continuous_fst).sub
    ((_root_.GD.N0106.N0428.N0770.N1725.d024133 (1 - c) w).comp continuous_fst)).mul
      ((_root_.GD.N0106.N0428.N0770.N1725.d024133 f w).comp continuous_snd)

theorem d024135 : Continuous _root_.GD.N0106.N0428.N0770.N1725.d024130 := by
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (_root_.GD.N0106.N0428.N0770.N1725.d024134 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i) (_root_.GD.N0106.N0428.N0770.N1725.d024128 i) _root_.GD.N0106.N0428.N0770.N1725.d024116)

theorem d024136 : Continuous _root_.GD.N0106.N0428.N0770.N1725.d024131 := by
  exact (continuous_const.mul (_root_.GD.N0106.N0428.N0770.N1725.d024134 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118)).sub
    (continuous_const.mul (_root_.GD.N0106.N0428.N0770.N1725.d024134 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118))

theorem d024137 : Measurable _root_.GD.N0106.N0428.N0770.N1725.d024130 := _root_.GD.N0106.N0428.N0770.N1725.d024135.measurable
theorem d024138 : Measurable _root_.GD.N0106.N0428.N0770.N1725.d024131 := _root_.GD.N0106.N0428.N0770.N1725.d024136.measurable

theorem d024139 (c w x : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x := le_max_right _ _

theorem d024140 (c w x : ℝ) (hw : 0 < w) : _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ≤ 1 := by
  apply max_le _ zero_le_one
  have h := div_nonneg (abs_nonneg (x - c)) hw.le
  linarith

theorem d024141 (c f w : ℝ) (p : ℝ × ℝ) (hw : 0 < w) :
    |_root_.GD.N0106.N0428.N0770.N1725.d024126 c f w p| ≤ 1 := by
  have hc0 := _root_.GD.N0106.N0428.N0770.N1725.d024139 c w p.1
  have hc1 := _root_.GD.N0106.N0428.N0770.N1725.d024140 c w p.1 hw
  have hr0 := _root_.GD.N0106.N0428.N0770.N1725.d024139 (1 - c) w p.1
  have hr1 := _root_.GD.N0106.N0428.N0770.N1725.d024140 (1 - c) w p.1 hw
  have hd : |_root_.GD.N0106.N0428.N0770.N1725.d024124 c w p.1 - _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 - c) w p.1| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024126, abs_mul, abs_of_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024139 f w p.2)]
  calc
    _ ≤ 1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f w p.2 := mul_le_mul_of_nonneg_right hd (_root_.GD.N0106.N0428.N0770.N1725.d024139 f w p.2)
    _ ≤ 1 := by simpa only [one_mul] using _root_.GD.N0106.N0428.N0770.N1725.d024140 f w p.2 hw

theorem d024142 (p : ℝ × ℝ) : |_root_.GD.N0106.N0428.N0770.N1725.d024130 p| < 1 := by
  have hsum : |_root_.GD.N0106.N0428.N0770.N1725.d024130 p| ≤ ∑ i : Fin 4, |_root_.GD.N0106.N0428.N0770.N1725.d024129 i| := by
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024130
    calc
      _ ≤ ∑ i : Fin 4,
          |_root_.GD.N0106.N0428.N0770.N1725.d024129 i * _root_.GD.N0106.N0428.N0770.N1725.d024126 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i) (_root_.GD.N0106.N0428.N0770.N1725.d024128 i) _root_.GD.N0106.N0428.N0770.N1725.d024116 p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 4, |_root_.GD.N0106.N0428.N0770.N1725.d024129 i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (_root_.GD.N0106.N0428.N0770.N1725.d024141 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i) (_root_.GD.N0106.N0428.N0770.N1725.d024128 i) _root_.GD.N0106.N0428.N0770.N1725.d024116 p _root_.GD.N0106.N0428.N0770.N1725.d024120)
          (abs_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024129 i))
  have hc : (∑ i : Fin 4, |_root_.GD.N0106.N0428.N0770.N1725.d024129 i|) < 1 := by
    norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024129, Fin.sum_univ_succ]
  exact hsum.trans_lt hc

theorem d024143 (p : ℝ × ℝ) : |_root_.GD.N0106.N0428.N0770.N1725.d024131 p| ≤ 7 := by
  have hA := _root_.GD.N0106.N0428.N0770.N1725.d024141 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p _root_.GD.N0106.N0428.N0770.N1725.d024121
  have hB := _root_.GD.N0106.N0428.N0770.N1725.d024141 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p _root_.GD.N0106.N0428.N0770.N1725.d024121
  calc
    |_root_.GD.N0106.N0428.N0770.N1725.d024131 p| ≤ |3 * _root_.GD.N0106.N0428.N0770.N1725.d024126 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p| +
        |4 * _root_.GD.N0106.N0428.N0770.N1725.d024126 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p| := abs_sub _ _
    _ ≤ 7 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith

theorem d024144 (c w x : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 - c) w (1 - x) = _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024124
  rw [show (1 - x) - (1 - c) = -(x - c) by ring, abs_neg]

theorem d024145 (c f w : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024126 c f w (1 - p.1, p.2) = -_root_.GD.N0106.N0428.N0770.N1725.d024126 c f w p := by
  have hc : _root_.GD.N0106.N0428.N0770.N1725.d024124 c w (1 - p.1) = _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 - c) w p.1 := by
    simpa only [sub_sub_cancel] using _root_.GD.N0106.N0428.N0770.N1725.d024144 (1 - c) w p.1
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024126, hc, _root_.GD.N0106.N0428.N0770.N1725.d024144]
  ring

theorem d024146 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024130 (1 - p.1, p.2) = -_root_.GD.N0106.N0428.N0770.N1725.d024130 p := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024130, _root_.GD.N0106.N0428.N0770.N1725.d024145, mul_neg, Finset.sum_neg_distrib]

theorem d024147 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024131 (1 - p.1, p.2) = -_root_.GD.N0106.N0428.N0770.N1725.d024131 p := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024131, _root_.GD.N0106.N0428.N0770.N1725.d024145]
  ring

theorem d024148 (F : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024130 (1 / 2, F) = 0 := by
  have h := _root_.GD.N0106.N0428.N0770.N1725.d024146 (1 / 2, F)
  norm_num only at h
  linarith

theorem d024149 (F : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024131 (1 / 2, F) = 0 := by
  have h := _root_.GD.N0106.N0428.N0770.N1725.d024147 (1 / 2, F)
  norm_num only at h
  linarith



theorem d024150 (c w x : ℝ) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x = w * _root_.GD.N0118.d008582 c w x := by
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024067 c w x hw]
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024124
  rw [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

theorem d024151 (c f w : ℝ) (p : ℝ × ℝ)
    (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p = w ^ 2 * _root_.GD.N0118.d008583 c f w p := by
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024125, _root_.GD.N0106.N0428.N0770.N1725.d024150 c w p.1 hw,
    _root_.GD.N0106.N0428.N0770.N1725.d024150 f w p.2 hw]
  unfold _root_.GD.N0118.d008583
  ring

theorem d024152 (c f w : ℝ) (hw : 0 < w) :
    ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume) = w ^ 2 := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024151 c f w _ hw]
  rw [integral_const_mul, _root_.GD.N0118.d008601 c f w hw, mul_one]

theorem d024153 (c f w : ℝ) (hw : 0 < w) :
    ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume) = 4 * w ^ 2 / 9 := by
  have heq : (fun p => _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2) =
      fun p => w ^ 4 * _root_.GD.N0118.d008583 c f w p ^ 2 := by
    funext p
    rw [_root_.GD.N0106.N0428.N0770.N1725.d024151 c f w p hw]
    ring
  rw [heq, integral_const_mul, _root_.GD.N0118.d008602 c f w hw]
  field_simp [hw.ne']
  <;> ring



def d024154 (a t : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + a * _root_.GD.N0106.N0428.N0770.N1725.d024130 p + t * _root_.GD.N0106.N0428.N0770.N1725.d024131 p

def d024155 (xbar ybar vx vy : ℝ) : ℝ × ℝ := by
  classical
  exact if vx + vy = 0 then (1 / 2, 0)
    else (vy / (vx + vy), 2 * (xbar - ybar) ^ 2 / (vx + vy))


def d024156 (a t xbar ybar vx vy : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1437.d003016 (fun e F => _root_.GD.N0106.N0428.N0770.N1725.d024154 a t (e, F))
    xbar ybar (vx / 2) (vy / 2)

def d024157 := _root_.GD.N0106.N0428.N0770.N1725.d024156 0 0
def d024158 := _root_.GD.N0106.N0428.N0770.N1725.d024156 _root_.GD.N0106.N0428.N0770.N1725.d024117 0
def d024159 := _root_.GD.N0106.N0428.N0770.N1725.d024156 _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119

theorem d024160 (vx vy : ℝ) :
    _root_.GD.N0232.N0720.N1437.d002996 (vx / 2) (vy / 2) = vy / (vx + vy) := by
  unfold _root_.GD.N0232.N0720.N1437.d002996
  rw [← add_div]
  by_cases h : vx + vy = 0
  · simp [h]
  · field_simp [h]
    <;> ring

theorem d024161 (xbar ybar vx vy : ℝ) :
    _root_.GD.N0232.N0720.N1437.d002997 xbar ybar (vx / 2) (vy / 2) =
      2 * (xbar - ybar) ^ 2 / (vx + vy) := by
  unfold _root_.GD.N0232.N0720.N1437.d002997
  rw [← add_div]
  by_cases h : vx + vy = 0
  · simp [h]
  · field_simp [h]
    <;> ring

theorem d024162 (a t xbar ybar vx vy : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024156 a t xbar ybar vx vy =
      ybar + (xbar - ybar) * _root_.GD.N0106.N0428.N0770.N1725.d024154 a t (_root_.GD.N0106.N0428.N0770.N1725.d024155 xbar ybar vx vy) := by
  by_cases h : vx + vy = 0
  · have hz : ¬ _root_.GD.N0232.N0720.N1437.d003012 (vx / 2) (vy / 2) := by
      unfold _root_.GD.N0232.N0720.N1437.d003012
      rw [← add_div, h]
      simp
    rw [_root_.GD.N0106.N0428.N0770.N1725.d024156, _root_.GD.N0232.N0720.N1437.d003019 _ _ _ _ _ hz]
    simp only [_root_.GD.N0106.N0428.N0770.N1725.d024155, h, if_true, _root_.GD.N0106.N0428.N0770.N1725.d024154, _root_.GD.N0106.N0428.N0770.N1725.d024148, _root_.GD.N0106.N0428.N0770.N1725.d024149,
      mul_zero, add_zero]
    ring
  · have hn : _root_.GD.N0232.N0720.N1437.d003012 (vx / 2) (vy / 2) := by
      unfold _root_.GD.N0232.N0720.N1437.d003012
      rw [← add_div]
      exact div_ne_zero h (by norm_num)
    rw [_root_.GD.N0106.N0428.N0770.N1725.d024156, _root_.GD.N0232.N0720.N1437.d003018 _ _ _ _ _ hn]
    simp only [_root_.GD.N0232.N0720.N1437.d002998, _root_.GD.N0106.N0428.N0770.N1725.d024160, _root_.GD.N0106.N0428.N0770.N1725.d024161,
      _root_.GD.N0106.N0428.N0770.N1725.d024155, h, if_false]

theorem d024163 (xbar ybar vx vy : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024158 xbar ybar vx vy = _root_.GD.N0106.N0428.N0770.N1725.d024157 xbar ybar vx vy +
      _root_.GD.N0106.N0428.N0770.N1725.d024117 * (xbar - ybar) * _root_.GD.N0106.N0428.N0770.N1725.d024130 (_root_.GD.N0106.N0428.N0770.N1725.d024155 xbar ybar vx vy) := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024158, _root_.GD.N0106.N0428.N0770.N1725.d024157, _root_.GD.N0106.N0428.N0770.N1725.d024162, _root_.GD.N0106.N0428.N0770.N1725.d024154]
  ring

theorem d024164 (xbar ybar vx vy : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024159 xbar ybar vx vy = _root_.GD.N0106.N0428.N0770.N1725.d024158 xbar ybar vx vy +
      _root_.GD.N0106.N0428.N0770.N1725.d024119 * (xbar - ybar) * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1725.d024155 xbar ybar vx vy) := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024159, _root_.GD.N0106.N0428.N0770.N1725.d024158, _root_.GD.N0106.N0428.N0770.N1725.d024162, _root_.GD.N0106.N0428.N0770.N1725.d024154]
  ring

theorem d024165 (a t : ℝ) : _root_.GD.N0232.N0720.N1437.d003000 (_root_.GD.N0106.N0428.N0770.N1725.d024156 a t) := by
  intro shift dilation xbar ybar vx vy hd
  have h := _root_.GD.N0232.N0720.N1437.d003017
    (fun e F => _root_.GD.N0106.N0428.N0770.N1725.d024154 a t (e, F)) shift dilation
      xbar ybar (vx / 2) (vy / 2) hd
  simpa only [_root_.GD.N0106.N0428.N0770.N1725.d024156, mul_div_assoc] using h

theorem d024166 : Measurable
    (fun p : ℝ × ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024155 p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  have hz : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | p.2.2.1 + p.2.2.2 = 0} :=
    measurableSet_eq_fun (measurable_snd.snd.fst.add measurable_snd.snd.snd)
      measurable_const
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024155
  apply Measurable.ite hz
  · exact measurable_const
  · fun_prop

theorem d024167 (a t : ℝ) : Measurable (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t) :=
  (measurable_fst.add (measurable_const.mul _root_.GD.N0106.N0428.N0770.N1725.d024137)).add
    (measurable_const.mul _root_.GD.N0106.N0428.N0770.N1725.d024138)

theorem d024168 (a t : ℝ) : Measurable
    (fun p : ℝ × ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024156 a t p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024162]
  exact measurable_snd.fst.add
    ((measurable_fst.sub measurable_snd.fst).mul
      ((_root_.GD.N0106.N0428.N0770.N1725.d024167 a t).comp _root_.GD.N0106.N0428.N0770.N1725.d024166))



def d024169 (q e F : ℝ) : ℝ := e + (1 - 2 * e + F) * q - F * q ^ 2
def d024170 (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (p.2 / (p.1 * (1 - p.1))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 q p.1 p.2 ^ (-(5 / 2 : ℝ))

theorem d024171 (q e F : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F = q * (1 - e) + (1 - q) * e + F * q * (1 - q) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
  ring

theorem d024172 {q e F : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) 1) (hF : 0 < F) : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024171]
  by_cases hq0 : q = 0
  · simpa [hq0] using he.1
  · have hqp : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hq0)
    have hfirst : 0 < q * (1 - e) := mul_pos hqp (sub_pos.mpr he.2)
    have hsecond : 0 ≤ (1 - q) * e := mul_nonneg (sub_nonneg.mpr hq.2) he.1.le
    have hthird : 0 ≤ F * q * (1 - q) :=
      mul_nonneg (mul_nonneg hF.le hq.1) (sub_nonneg.mpr hq.2)
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hfirst hsecond) hthird

private theorem d024173 {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  simp only [one_div]

theorem d024174 {q e F : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) 1) (hF : 0 < F) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) = Real.sqrt (F / (e * (1 - e))) /
      (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 * Real.sqrt (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)) := by
  have hN := _root_.GD.N0106.N0428.N0770.N1725.d024172 hq he hF
  have hp : _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ (-(5 / 2 : ℝ)) =
      1 / (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 * Real.sqrt (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)) := by
    rw [Real.rpow_neg hN.le, show (5 / 2 : ℝ) = 2 + 1 / 2 by ring,
      Real.rpow_add hN, Real.rpow_two, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  change Real.sqrt (F / (e * (1 - e))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ (-(5 / 2 : ℝ)) = _
  rw [hp]
  simp only [div_eq_mul_inv, one_mul]

theorem d024175 {q e F : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) 1) (hF : 0 < F) :
    _root_.GD.N0120.d008811 (1 / 2) (1 / 2) q (e, F) =
      (2 : ℝ) ^ (5 / 2 : ℝ) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by
  have hN := _root_.GD.N0106.N0428.N0770.N1725.d024172 hq he hF
  have hEc : 0 < 1 - e := sub_pos.mpr he.2
  have hfront : e ^ (-(1 / 2 : ℝ)) * (1 - e) ^ (-(1 / 2 : ℝ)) *
      F ^ (1 / 2 : ℝ) = Real.sqrt (F / (e * (1 - e))) := by
    rw [_root_.GD.N0106.N0428.N0770.N1725.d024173 he.1, _root_.GD.N0106.N0428.N0770.N1725.d024173 hEc, ← Real.sqrt_eq_rpow,
      Real.sqrt_div hF.le, Real.sqrt_mul he.1.le]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr he.1), ne_of_gt (Real.sqrt_pos.mpr hEc)]
  have hden : (1 / 2 : ℝ) * q * (1 - e) + (1 / 2 : ℝ) * (1 - q) * e +
      F * q * (1 - q) / 2 = _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F / 2 := by
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
    ring
  have hscale : (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F / 2) ^ (-(5 / 2 : ℝ)) =
      (2 : ℝ) ^ (5 / 2 : ℝ) * _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ (-(5 / 2 : ℝ)) := by
    rw [Real.div_rpow hN.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  unfold _root_.GD.N0120.d008811 _root_.GD.N0116.d006509
  norm_num only
  rw [hfront, hden, hscale]
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024170
  ring

theorem d024176 {q e F : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) 1) (hF : 0 < F) :
    _root_.GD.N0116.d006511 (1 / 2) (1 / 2) q (e, F) =
      (3 / (2 * Real.pi)) * (q * (1 - q)) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by
  rw [_root_.GD.N0120.d008818,
    _root_.GD.N0106.N0428.N0770.N1725.d024175 hq he hF]
  have hc := _root_.GD.N0232.N0720.N1487.d013916
  unfold _root_.GD.N0120.d008813 _root_.GD.N0116.d006508
  norm_num only [Real.rpow_two]
  calc
    _ = (_root_.GD.N0116.d006507 (1 / 2) (1 / 2) *
        (2 : ℝ) ^ (5 / 2 : ℝ)) * (q * (1 - q)) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by ring
    _ = _ := by rw [hc]



theorem d024177 (S : ℝ) {q e F : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (he : e ∈ Ioo (0 : ℝ) 1) (hF : 0 < F) :
    (S / 2) * _root_.GD.N0116.d006511 (1 / 2) (1 / 2) q (e, F) =
      (3 * S / (4 * Real.pi)) * (q * (1 - q)) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024176 hq he hF]
  ring

end
end GD.N0106.N0428.N0770.N1725

#print axioms _root_.GD.N0106.N0428.N0770.N1725.d024168
