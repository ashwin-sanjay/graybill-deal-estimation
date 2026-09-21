import GD.Module1866
import GD.Module0347

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0082.N0331

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1066 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0602
open _root_.GD.N0076.N0313
open _root_.GD.N0081.N0326

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030613
    (d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) (he : e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (τ : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hτ : ∀ θ, τ θ ∈ Ioo (0 : ℝ) 1)
    (p q : ℝ → ℝ)
    (hp0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ p t)
    (hq0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ q t)
    (hpcont : ContinuousOn p (Ioo 0 1))
    (hp : ∀ t ∈ Ioo (0 : ℝ) 1, p t < 1)
    (hqcont : ContinuousOn q (Icc 0 1))
    (hqleft : q 0 < 1) (hqright : q 1 < 1)
    (hpd : ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ d ≤ ENNReal.ofReal (p (τ θ)))
    (hqe : ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ e ≤ ENNReal.ofReal (q (τ θ))) :
    _root_.GD.N0082.d030603 m n hm hn := by
  obtain ⟨ε, γ, hε, hε1, hγ, hmix⟩ := _root_.GD.N0081.N0326.d005152
    p q hpcont hp hqcont hqleft hqright
  obtain ⟨J, hJ, hJcap⟩ := _root_.GD.N0082.d030601 (show 1 - γ < 1 by linarith)
  have ha : 0 ≤ 1 - ε := (sub_pos.mpr hε1).le
  have hmd := _root_.GD.N0232.N0720.N1215.d014285 m n d hd.1
    (hd.2 _root_.GD.N0232.N0720.N1080.d014169)
  have hme := _root_.GD.N0232.N0720.N1215.d014285 m n e he.1
    (he.2 _root_.GD.N0232.N0720.N1080.d014169)
  let D := hmd.toLp d
  let E := hme.toLp e
  let s := (1 - ε) • D + ε • E
  refine ⟨J, hJ, _root_.GD.N0232.N0720.N1214.d014265 m n s, _root_.GD.N0232.N0720.N1214.d014266 m n s, ?_⟩
  intro θ
  have hpraw : _root_.GD.N0232.N0720.N1080.d014182 m n θ D ≤
      ENNReal.ofReal (p (τ θ)) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ := by
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ d hmd]
    exact (ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)).mp (hpd θ)
  have hqraw : _root_.GD.N0232.N0720.N1080.d014182 m n θ E ≤
      ENNReal.ofReal (q (τ θ)) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ := by
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ e hme]
    exact (ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)).mp (hqe θ)
  rw [_root_.GD.N0232.N0720.N1215.d014286]
  calc
    _root_.GD.N0232.N0720.N1080.d014182 m n θ s ≤ ENNReal.ofReal (1 - ε) * _root_.GD.N0232.N0720.N1080.d014182 m n θ D +
        ENNReal.ofReal ε * _root_.GD.N0232.N0720.N1080.d014182 m n θ E :=
      _root_.GD.N0230.N0602.d000121 (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
        θ.location D E ha hε.le (by ring)
    _ ≤ ENNReal.ofReal (1 - ε) *
          (ENNReal.ofReal (p (τ θ)) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) +
        ENNReal.ofReal ε *
          (ENNReal.ofReal (q (τ θ)) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) :=
      add_le_add (mul_le_mul' le_rfl hpraw) (mul_le_mul' le_rfl hqraw)
    _ = ENNReal.ofReal ((1 - ε) * p (τ θ) + ε * q (τ θ)) *
          _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ := by
      rw [ENNReal.ofReal_add (mul_nonneg ha (hp0 _ (hτ θ)))
        (mul_nonneg hε.le (hq0 _ (hτ θ))),
        ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hε.le, add_mul]
      simp only [mul_assoc]
    _ ≤ ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal ((hmix _ (hτ θ)).trans hJcap.le)) le_rfl

theorem d030614
    (d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) (he : e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (τ : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hτ : ∀ θ, τ θ ∈ Ioo (0 : ℝ) 1)
    (p q : ℝ → ℝ)
    (hp0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ p t)
    (hq0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ q t)
    (hpcont : ContinuousOn p (Ioo 0 1))
    (hp : ∀ t ∈ Ioo (0 : ℝ) 1, p t < 1)
    (hqcont : ContinuousOn q (Icc 0 1))
    (hqleft : q 0 < 1) (hqright : q 1 < 1)
    (hpd : ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ d ≤ ENNReal.ofReal (p (τ θ)))
    (hqe : ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ e ≤ ENNReal.ofReal (q (τ θ))) :
    ¬ _root_.GD.N0082.d030602 m n hm hn :=
  (_root_.GD.N0082.d030610 m n hm hn).mpr
    (_root_.GD.N0082.N0331.d030613 m n hm hn d e hd he τ hτ p q hp0 hq0
      hpcont hp hqcont hqleft hqright hpd hqe)

end

end GD.N0082.N0331

#print axioms _root_.GD.N0082.N0331.d030613
#print axioms _root_.GD.N0082.N0331.d030614
