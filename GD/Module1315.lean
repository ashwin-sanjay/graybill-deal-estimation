import GD.Module1314






















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Topology
open scoped Topology

namespace GD.N0106.N0428.N0765.N1520
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672
open _root_.GD.N0106.N0428.N0765.N1526 _root_.GD.N0106.N0428.N0765.N1528 _root_.GD.N0106.N0428.N0765.N1527
open _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521


def d021477 (e a b x : ℝ) : ℝ :=
  (Real.exp b * (1 - x) + x) * ((1 - x) + e * x) +
    (1 + e) * Real.exp a * (1 + Real.exp b) * x * (1 - x)

theorem d021478 (e a b x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1526.d021435 e a b x = _root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x := by
  unfold _root_.GD.N0106.N0428.N0765.N1526.d021435 _root_.GD.N0106.N0428.N0765.N1526.d021431 _root_.GD.N0106.N0428.N0765.N1526.d021432 _root_.GD.N0106.N0428.N0765.N1526.d021433 _root_.GD.N0106.N0428.N0765.N1526.d021434 _root_.GD.N0106.N0428.N0765.N1663.d021403 _root_.GD.N0106.N0428.N0765.N1520.d021477
  ring


theorem d021479 (e a b x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b 0 0 x = (_root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1526.d021439]
  simp only [add_zero, _root_.GD.N0106.N0428.N0765.N1538.d021187]
  simpa only [_root_.GD.N0106.N0428.N0765.N1526.d021435, Complex.ofReal_add] using
    congrArg Complex.ofReal (_root_.GD.N0106.N0428.N0765.N1520.d021478 e a b x)


theorem d021480 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b α β : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ ≤ _root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x := by
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GD.N0106.N0428.N0765.N1526.d021438 he hx a b
  rw [_root_.GD.N0106.N0428.N0765.N1526.d021439]
  calc
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021431 e b x) β + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021432 e x) 0 +
        _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021433 e a x) α + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021434 e a b x) (α + β)‖
      ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021431 e b x) β‖ + ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021432 e x) 0‖ +
        ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021433 e a x) α‖ + ‖_root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021434 e a b x) (α + β)‖ :=
      (norm_add_le _ _).trans
        (_root_.add_le_add ((norm_add_le _ _).trans
          (_root_.add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ = _root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x := by
      rw [_root_.GD.N0106.N0428.N0765.N1538.d021188 h1, _root_.GD.N0106.N0428.N0765.N1538.d021188 h2, _root_.GD.N0106.N0428.N0765.N1538.d021188 h3, _root_.GD.N0106.N0428.N0765.N1538.d021188 h4]
      exact _root_.GD.N0106.N0428.N0765.N1520.d021478 e a b x


theorem d021481 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b α β : ℝ) (hs : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x ≤
      ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ := by
  have hrot := _root_.GD.N0106.N0428.N0765.N1526.d021441 he hx a b α β
    (_root_.GD.N0106.N0428.N0765.N1538.d021191 α β) (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) (by linarith [Real.pi_pos])
    (_root_.GD.N0106.N0428.N0765.N1538.d021195 α β) (_root_.GD.N0106.N0428.N0765.N1538.d021196 α β) (_root_.GD.N0106.N0428.N0765.N1538.d021197 α β) (_root_.GD.N0106.N0428.N0765.N1538.d021198 α β)
  calc
    Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x =
        Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1526.d021435 e a b x := by
      rw [_root_.GD.N0106.N0428.N0765.N1520.d021478]
    _ ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x).re := hrot
    _ ≤ |(_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x).re| := le_abs_self _
    _ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ := Complex.abs_re_le_norm _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ := by
      rw [norm_mul, _root_.GD.N0106.N0428.N0765.N1538.d021216, one_mul]


theorem d021482 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b α β : ℝ) (hs : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x ≤
        ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ ∧
      ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ ≤ _root_.GD.N0106.N0428.N0765.N1520.d021477 e a b x :=
  ⟨_root_.GD.N0106.N0428.N0765.N1520.d021481 he hx a b α β hs, _root_.GD.N0106.N0428.N0765.N1520.d021480 he hx a b α β⟩


def d021483 (e a b α β : ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β


def d021484 (e a b : ℝ) : ℝ := (_root_.GD.N0106.N0428.N0765.N1520.d021483 e a b 0 0).re


def d021485 (α β : ℝ) : ℝ :=
  Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹

private theorem d021486 : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1538.d021192, abs_zero, add_zero, mul_zero] using Real.pi_pos

theorem d021487 {α β : ℝ}
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : 0 < _root_.GD.N0106.N0428.N0765.N1520.d021485 α β := by
  exact mul_pos
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1538.d021219 (_root_.GD.N0106.N0428.N0765.N1538.d021233 hs)) _)
    (inv_pos.mpr (_root_.GD.N0106.N0428.N0765.N1538.d021232 hs))


theorem d021488 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b = e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) := by
  have hr : _root_.GD.N0106.N0428.N0765.N1520.d021483 e a b 0 0 =
      ((e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) : ℝ) : ℂ) := by
    rw [_root_.GD.N0106.N0428.N0765.N1520.d021483, ← _root_.GD.N0106.N0428.N0765.N1672.d021429 he a b 0 0 (_root_.GD.N0106.N0428.N0765.N1538.d021233 _root_.GD.N0106.N0428.N0765.N1520.d021486)]
    exact _root_.GD.N0106.N0428.N0765.N1527.d021472 he a b
  unfold _root_.GD.N0106.N0428.N0765.N1520.d021484
  rw [hr, Complex.ofReal_re]


theorem d021489 (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1520.d021484 0 a b = (11 / 8 : ℝ) * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 /
      (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 + _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2) := by
  unfold _root_.GD.N0106.N0428.N0765.N1520.d021484 _root_.GD.N0106.N0428.N0765.N1520.d021483
  rw [_root_.GD.N0106.N0428.N0765.N1527.d021475, Complex.ofReal_re]

theorem d021490 (a b α β : ℝ)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1520.d021483 e a b α β) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1520.d021483 0 a b α β)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1520.d021483] using _root_.GD.N0106.N0428.N0765.N1528.d021467 a b α β hs

theorem d021491 (a b : ℝ) :
    Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1520.d021484 0 a b)) := by
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (_root_.GD.N0106.N0428.N0765.N1520.d021490 a b 0 0 _root_.GD.N0106.N0428.N0765.N1520.d021486)


theorem d021492 {e : ℝ} (he : 0 < e)
    (a b α β : ℝ) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1520.d021483 e a b α β‖ ≤ _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b := by
  rw [_root_.GD.N0106.N0428.N0765.N1520.d021488 he]
  have h := _root_.GD.N0106.N0428.N0765.N1538.d021259 he a b α β hs
  rw [_root_.GD.N0106.N0428.N0765.N1672.d021429 he a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hs)] at h
  exact h



theorem d021493 (a b α β : ℝ)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1520.d021483 0 a b α β‖ ≤ _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * _root_.GD.N0106.N0428.N0765.N1520.d021484 0 a b := by
  apply le_of_tendsto_of_tendsto (_root_.GD.N0106.N0428.N0765.N1520.d021490 a b α β hs).norm
    ((_root_.GD.N0106.N0428.N0765.N1520.d021491 a b).const_mul (_root_.GD.N0106.N0428.N0765.N1520.d021485 α β))
  filter_upwards [self_mem_nhdsWithin] with e he
  exact _root_.GD.N0106.N0428.N0765.N1520.d021492 he a b α β hs


theorem d021494 {e : ℝ} (he : 0 ≤ e)
    (a b α β : ℝ) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1520.d021483 e a b α β‖ ≤ _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b := by
  rcases eq_or_lt_of_le he with heq | hepos
  · subst e
    exact _root_.GD.N0106.N0428.N0765.N1520.d021493 a b α β hs
  · exact _root_.GD.N0106.N0428.N0765.N1520.d021492 hepos a b α β hs

theorem d021495 {e : ℝ} (he : 0 ≤ e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b ≤ (3 / 2 : ℝ) * Real.exp b := by
  rcases eq_or_lt_of_le he with heq | hepos
  · subst e
    apply le_of_tendsto (_root_.GD.N0106.N0428.N0765.N1520.d021491 a b)
    filter_upwards [self_mem_nhdsWithin] with e he
    rw [_root_.GD.N0106.N0428.N0765.N1520.d021488 he]
    exact _root_.GD.N0106.N0428.N0765.N1538.d021260 he a b
  · rw [_root_.GD.N0106.N0428.N0765.N1520.d021488 hepos]
    exact _root_.GD.N0106.N0428.N0765.N1538.d021260 hepos a b



theorem d021496 {e : ℝ} (he : 0 ≤ e)
    (a b α β : ℝ) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1520.d021483 e a b α β‖ ≤ _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b ∧
      _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b ≤
        (3 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * Real.exp b := by
  refine ⟨_root_.GD.N0106.N0428.N0765.N1520.d021494 he a b α β hs, ?_⟩
  calc
    _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * _root_.GD.N0106.N0428.N0765.N1520.d021484 e a b ≤
        _root_.GD.N0106.N0428.N0765.N1520.d021485 α β * ((3 / 2 : ℝ) * Real.exp b) :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1520.d021495 he a b) (_root_.GD.N0106.N0428.N0765.N1520.d021487 hs).le
    _ = _ := by ring

end
end GD.N0106.N0428.N0765.N1520

#print axioms _root_.GD.N0106.N0428.N0765.N1520.d021482
#print axioms _root_.GD.N0106.N0428.N0765.N1520.d021493
#print axioms _root_.GD.N0106.N0428.N0765.N1520.d021496

