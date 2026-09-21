import GD.Module1308
import GD.Module1317
import GD.Module0368











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1537
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1675 _root_.GD.N0106.N0428.N0765.N1584
open _root_.GD.N0106.N0428.N0765.N1585 _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521

def d021524 (x θ : ℝ) : ℂ := (x : ℂ) + (θ : ℂ) * Complex.I

@[simp] theorem d021525 (x θ : ℝ) : (_root_.GD.N0106.N0428.N0765.N1537.d021524 x θ).re = x := by
  simp [_root_.GD.N0106.N0428.N0765.N1537.d021524]

@[simp] theorem d021526 (x θ : ℝ) : (_root_.GD.N0106.N0428.N0765.N1537.d021524 x θ).im = θ := by
  simp [_root_.GD.N0106.N0428.N0765.N1537.d021524]

def d021527 (α β : ℝ) (p : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 (_root_.GD.N0106.N0428.N0765.N1537.d021524 p.1 α) *
    _root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 (_root_.GD.N0106.N0428.N0765.N1537.d021524 p.2 β)

def d021528 (α β : ℝ) : ℝ :=
  Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * Real.cos (β / 2) ^ (-(10 : ℝ))

def d021529 (β : ℝ) : ℝ := (Real.cos (β / 2))⁻¹


def d021530 (e β b : ℝ) : ℂ :=
  Complex.exp (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β) / (1 + (e : ℂ) * Complex.exp (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β))

def d021531 (e : ℝ) : ℝ := (1 + e)⁻¹


def d021532 (e α β : ℝ) (p : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1537.d021527 α β p *
    ((_root_.GD.N0106.N0428.N0765.N1537.d021530 e β p.2 - _root_.GD.N0106.N0428.N0765.N1537.d021531 e) ^ 2 -
      (_root_.GD.N0106.N0428.N0765.N1675.d021510 e α β p - _root_.GD.N0106.N0428.N0765.N1537.d021531 e) ^ 2)

def d021533 (α β : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1537.d021528 α β * _root_.GD.N0106.N0428.N0765.N1521.d020868 p *
    ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β * Real.exp p.2 + 1)^2 +
      (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β * Real.exp p.2 + 1)^2)

def d021534 (α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1537.d021528 α β *
    ((5 / 2) * ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β)^2 + (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2) +
      (5 / 2) * (_root_.GD.N0106.N0428.N0765.N1537.d021529 β + _root_.GD.N0106.N0428.N0765.N1675.d021511 α β) + 2)

theorem d021535 {α β : ℝ}
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    |α| < Real.pi / 2 ∧ |β| < Real.pi / 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021192 at hw
  constructor <;> nlinarith [abs_nonneg α, abs_nonneg β, Real.pi_pos]



theorem d021536 {α β : ℝ} (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β ≤ 7 / 25) :
    ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi := by
  nlinarith [Real.pi_gt_three]

theorem d021537 {α β : ℝ}
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : 0 < _root_.GD.N0106.N0428.N0765.N1537.d021528 α β := by
  obtain ⟨ha, hb⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hw
  exact mul_pos (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1585.d005527 ha) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1585.d005527 hb) _)

theorem d021538 {β : ℝ} (hb : |β| < Real.pi / 2) : 0 < _root_.GD.N0106.N0428.N0765.N1537.d021529 β :=
  inv_pos.mpr (_root_.GD.N0106.N0428.N0765.N1585.d005527 hb)

theorem d021539 {α β : ℝ}
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (p : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1537.d021527 α β p‖ ≤ _root_.GD.N0106.N0428.N0765.N1537.d021528 α β * _root_.GD.N0106.N0428.N0765.N1521.d020868 p := by
  obtain ⟨ha, hb⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hw
  have hA := _root_.GD.N0106.N0428.N0765.N1585.d005537 (z := _root_.GD.N0106.N0428.N0765.N1537.d021524 p.1 α) (by simpa using ha)
  have hB := _root_.GD.N0106.N0428.N0765.N1585.d005538 (z := _root_.GD.N0106.N0428.N0765.N1537.d021524 p.2 β) (by simpa using hb)
  simp only [_root_.GD.N0106.N0428.N0765.N1537.d021526, _root_.GD.N0106.N0428.N0765.N1537.d021525] at hA hB
  have hA0 : 0 ≤ Real.cos (α / 2)^(-((23 : ℝ) / 2)) *
      _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 p.1 :=
    mul_nonneg (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1585.d005527 ha).le _)
      (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) p.1).le
  calc ‖_root_.GD.N0106.N0428.N0765.N1537.d021527 α β p‖ =
      ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 (_root_.GD.N0106.N0428.N0765.N1537.d021524 p.1 α)‖ *
        ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 (_root_.GD.N0106.N0428.N0765.N1537.d021524 p.2 β)‖ := norm_mul _ _
    _ ≤ (Real.cos (α / 2)^(-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 p.1) *
        (Real.cos (β / 2)^(-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 p.2) :=
      mul_le_mul hA hB (norm_nonneg _) hA0
    _ = _root_.GD.N0106.N0428.N0765.N1537.d021528 α β * _root_.GD.N0106.N0428.N0765.N1521.d020868 p := by
      unfold _root_.GD.N0106.N0428.N0765.N1537.d021528 _root_.GD.N0106.N0428.N0765.N1521.d020868
      ring

theorem d021540 {e β : ℝ} (he : 0 ≤ e)
    (hb : |β| < Real.pi / 2) (b : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1537.d021530 e β b‖ ≤ _root_.GD.N0106.N0428.N0765.N1537.d021529 β * Real.exp b := by
  have hc := _root_.GD.N0106.N0428.N0765.N1585.d005527 hb
  have hl := _root_.GD.N0106.N0428.N0765.N1585.d005528 (x := 1) (y := e * Real.exp b)
    zero_le_one (mul_nonneg he (Real.exp_pos b).le)
    (le_of_lt (lt_trans hb (by linarith [Real.pi_pos])))
  have hden : (1 : ℂ) + (e : ℂ) * Complex.exp (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β) =
      1 + ((e * Real.exp b : ℝ) : ℂ) * Complex.exp ((β : ℂ) * Complex.I) := by
    rw [_root_.GD.N0106.N0428.N0765.N1585.d005531 (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β), _root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526]
    push_cast
    ring
  rw [Complex.ofReal_one, ← hden] at hl
  have hlow : Real.cos (β / 2) ≤
      ‖(1 : ℂ) + (e : ℂ) * Complex.exp (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β)‖ := by
    nlinarith [mul_nonneg he (Real.exp_pos b).le]
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021530
  rw [norm_div, Complex.norm_exp, _root_.GD.N0106.N0428.N0765.N1537.d021525]
  calc Real.exp b / ‖(1 : ℂ) + (e : ℂ) * Complex.exp (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β)‖ ≤
      Real.exp b / Real.cos (β / 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos b).le hc hlow
    _ = _root_.GD.N0106.N0428.N0765.N1537.d021529 β * Real.exp b := by unfold _root_.GD.N0106.N0428.N0765.N1537.d021529; ring

theorem d021541 {e : ℝ} (he : 0 ≤ e) :
    _root_.GD.N0106.N0428.N0765.N1537.d021531 e ∈ Icc (0 : ℝ) 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021531
  constructor
  · positivity
  · exact inv_le_one_of_one_le₀ (by linarith)

theorem d021542 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (p : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p‖ ≤ _root_.GD.N0106.N0428.N0765.N1537.d021533 α β p := by
  have hd := _root_.GD.N0106.N0428.N0765.N1537.d021539 hw p
  have hq := _root_.GD.N0106.N0428.N0765.N1585.d005545 (_root_.GD.N0106.N0428.N0765.N1537.d021540 he (_root_.GD.N0106.N0428.N0765.N1537.d021535 hw).2 p.2)
    (_root_.GD.N0106.N0428.N0765.N1675.d021513 he α β hw p) (_root_.GD.N0106.N0428.N0765.N1537.d021541 he).1 (_root_.GD.N0106.N0428.N0765.N1537.d021541 he).2
  exact (norm_mul _ _).trans_le
    (mul_le_mul hd hq (norm_nonneg _)
      (mul_nonneg (_root_.GD.N0106.N0428.N0765.N1537.d021537 hw).le (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)))


theorem d021543 (α β : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1537.d021533 α β p =
      (_root_.GD.N0106.N0428.N0765.N1537.d021528 α β * ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β)^2 + (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2)) *
        (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2)^2) +
      (2 * _root_.GD.N0106.N0428.N0765.N1537.d021528 α β * (_root_.GD.N0106.N0428.N0765.N1537.d021529 β + _root_.GD.N0106.N0428.N0765.N1675.d021511 α β)) *
        (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) +
      (2 * _root_.GD.N0106.N0428.N0765.N1537.d021528 α β) * _root_.GD.N0106.N0428.N0765.N1521.d020868 p := by
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021533
  ring


theorem d021544 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1537.d021533 0 0 p = _root_.GD.N0106.N0428.N0765.N1521.d020868 p *
      (2 + 5 * Real.exp p.2 + (13 / 4) * (Real.exp p.2)^2) := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1537.d021533, _root_.GD.N0106.N0428.N0765.N1537.d021528, _root_.GD.N0106.N0428.N0765.N1537.d021529, _root_.GD.N0106.N0428.N0765.N1675.d021511, _root_.GD.N0106.N0428.N0765.N1538.d021192, _root_.GD.N0106.N0428.N0765.N1538.d021231] <;>
    ring_nf <;> simp

theorem d021545 : _root_.GD.N0106.N0428.N0765.N1537.d021534 0 0 = 131 / 8 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1537.d021534, _root_.GD.N0106.N0428.N0765.N1537.d021528, _root_.GD.N0106.N0428.N0765.N1537.d021529, _root_.GD.N0106.N0428.N0765.N1675.d021511, _root_.GD.N0106.N0428.N0765.N1538.d021192, _root_.GD.N0106.N0428.N0765.N1538.d021231]

theorem d021546 (α β : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1537.d021533 α β) := by
  have h := ((_root_.GD.N0106.N0428.N0765.N1584.d021373.const_mul
      (_root_.GD.N0106.N0428.N0765.N1537.d021528 α β * ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β)^2 + (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2))).add
    (_root_.GD.N0106.N0428.N0765.N1584.d021372.const_mul
      (2 * _root_.GD.N0106.N0428.N0765.N1537.d021528 α β * (_root_.GD.N0106.N0428.N0765.N1537.d021529 β + _root_.GD.N0106.N0428.N0765.N1675.d021511 α β)))).add
        (_root_.GD.N0106.N0428.N0765.N1584.d021370.const_mul (2 * _root_.GD.N0106.N0428.N0765.N1537.d021528 α β))
  exact h.congr (Filter.Eventually.of_forall fun p => (_root_.GD.N0106.N0428.N0765.N1537.d021543 α β p).symm)

theorem d021547 (α β : ℝ) :
    (∫ p, _root_.GD.N0106.N0428.N0765.N1537.d021533 α β p) = _root_.GD.N0106.N0428.N0765.N1537.d021534 α β := by
  have hfun := funext (_root_.GD.N0106.N0428.N0765.N1537.d021543 α β)
  have h2 := _root_.GD.N0106.N0428.N0765.N1584.d021373.const_mul
    (_root_.GD.N0106.N0428.N0765.N1537.d021528 α β * ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β)^2 + (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β)^2))
  have h1 := _root_.GD.N0106.N0428.N0765.N1584.d021372.const_mul
    (2 * _root_.GD.N0106.N0428.N0765.N1537.d021528 α β * (_root_.GD.N0106.N0428.N0765.N1537.d021529 β + _root_.GD.N0106.N0428.N0765.N1675.d021511 α β))
  have h0 := _root_.GD.N0106.N0428.N0765.N1584.d021370.const_mul (2 * _root_.GD.N0106.N0428.N0765.N1537.d021528 α β)
  have ha := integral_add (h2.add h1) h0
  have hb := integral_add h2 h1
  simp only [Pi.add_apply] at ha hb
  rw [hfun, ha, hb, integral_const_mul, integral_const_mul, integral_const_mul,
    _root_.GD.N0106.N0428.N0765.N1584.d021375, _root_.GD.N0106.N0428.N0765.N1584.d021374, _root_.GD.N0106.N0428.N0765.N1584.d021371]
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021534
  ring

theorem d021548 (a b : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1585.d005529 a b) := by
  have hnum := Complex.measurable_exp.comp (measurable_id.const_mul (a : ℂ))
  have hbase : Measurable (fun z : ℂ => 1 + Complex.exp z) :=
    measurable_const.add Complex.measurable_exp
  have hp := (_root_.GD.N0106.N0428.N0765.N1675.d021514 ((a + b : ℝ) : ℂ)).comp hbase
  exact hnum.div (hp.const_mul (ProbabilityTheory.beta a b : ℂ))

@[fun_prop] theorem d021549 (e α β : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β) := by
  have hs1 : Measurable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021524 p.1 α) := by unfold _root_.GD.N0106.N0428.N0765.N1537.d021524; fun_prop
  have hs2 : Measurable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021524 p.2 β) := by unfold _root_.GD.N0106.N0428.N0765.N1537.d021524; fun_prop
  have hd : Measurable (_root_.GD.N0106.N0428.N0765.N1537.d021527 α β) :=
    ((_root_.GD.N0106.N0428.N0765.N1537.d021548 _ _).comp hs1).mul ((_root_.GD.N0106.N0428.N0765.N1537.d021548 _ _).comp hs2)
  have hg : Measurable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021530 e β p.2) := by
    unfold _root_.GD.N0106.N0428.N0765.N1537.d021530
    exact (Complex.measurable_exp.comp hs2).div
      (measurable_const.add ((Complex.measurable_exp.comp hs2).const_mul (e : ℂ)))
  exact hd.mul (((hg.sub measurable_const).pow_const 2).sub
    (((_root_.GD.N0106.N0428.N0765.N1675.d021518 e α β).sub measurable_const).pow_const 2))

theorem d021550 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : Integrable (_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β) := by
  exact Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1537.d021546 α β)
    (_root_.GD.N0106.N0428.N0765.N1537.d021549 e α β).aestronglyMeasurable
    (Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1537.d021542 he hw))

theorem d021551 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p‖) ≤ _root_.GD.N0106.N0428.N0765.N1537.d021534 α β := by
  rw [← _root_.GD.N0106.N0428.N0765.N1537.d021547]
  exact integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1537.d021550 he hw).norm
    (_root_.GD.N0106.N0428.N0765.N1537.d021546 α β) (Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1537.d021542 he hw))

theorem d021552 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖∫ p, _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p‖ ≤ _root_.GD.N0106.N0428.N0765.N1537.d021534 α β :=
  (norm_integral_le_integral_norm _).trans (_root_.GD.N0106.N0428.N0765.N1537.d021551 he hw)

theorem d021553 (β b : ℝ) :
    ContinuousAt (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021530 e β b) 0 := by
  have hc : ContinuousAt (fun e : ℝ => (e : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt
  have hd := (continuousAt_const (y := (1 : ℂ))).add
    (hc.mul (continuousAt_const (y := Complex.exp (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β))))
  exact (continuousAt_const (y := Complex.exp (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β))).div hd (by simp)

theorem d021554 : ContinuousAt _root_.GD.N0106.N0428.N0765.N1537.d021531 0 := by
  exact ((continuousAt_const (y := (1 : ℝ))).add continuousAt_id).inv₀ (by norm_num)

theorem d021555 (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (p : ℝ × ℝ) :
    Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1537.d021532 0 α β p)) := by
  have hg := (_root_.GD.N0106.N0428.N0765.N1537.d021553 β p.2).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have ho := (Complex.continuous_ofReal.continuousAt.comp
    _root_.GD.N0106.N0428.N0765.N1537.d021554).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hh := _root_.GD.N0106.N0428.N0765.N1528.d021467 p.1 p.2 α β hw
  exact (((hg.sub ho).pow 2).sub ((hh.sub ho).pow 2)).const_mul (_root_.GD.N0106.N0428.N0765.N1537.d021527 α β p)


theorem d021556 (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e : ℝ => ∫ p, _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p) (𝓝[>] 0)
      (𝓝 (∫ p, _root_.GD.N0106.N0428.N0765.N1537.d021532 0 α β p)) := by
  apply tendsto_integral_filter_of_dominated_convergence (_root_.GD.N0106.N0428.N0765.N1537.d021533 α β)
  · exact Filter.Eventually.of_forall fun e => (_root_.GD.N0106.N0428.N0765.N1537.d021549 e α β).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1537.d021542 (le_of_lt he) hw)
  · exact _root_.GD.N0106.N0428.N0765.N1537.d021546 α β
  · exact Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1537.d021555 α β hw)

end
end GD.N0106.N0428.N0765.N1537

#print axioms _root_.GD.N0106.N0428.N0765.N1537.d021542
#print axioms _root_.GD.N0106.N0428.N0765.N1537.d021547
#print axioms _root_.GD.N0106.N0428.N0765.N1537.d021550
#print axioms _root_.GD.N0106.N0428.N0765.N1537.d021552
#print axioms _root_.GD.N0106.N0428.N0765.N1537.d021556
