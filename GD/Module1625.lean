import GD.Module1624
import GD.Module1571































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory

namespace GD.N0106.N0428.N0770.N1742
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1207
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0106.N0428.N0770.N1726
open _root_.GD.N0106.N0428.N0770.N1741



def d027779 (mu sigma zeta a t : ℝ) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
    (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a t (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
      (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu)

theorem d027780 (a t sigma zeta : ℝ) :
    Measurable (fun x : ℝ × ℝ => (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2) :=
  ((_root_.GD.N0106.N0428.N0770.N1725.d024167 a t).sub measurable_const).pow_const 2


theorem d027781 (mu sigma zeta a t : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a t =
      _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta + _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta *
        ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2 := by
  have hkt : (∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 *
      (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta *
        ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2 :=
    _root_.GD.N0106.N0428.N0770.N1722.d024342 mu sigma zeta hsigma hzeta
      (fun x => (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2) (_root_.GD.N0106.N0428.N0770.N1742.d027780 a t sigma zeta)
  unfold _root_.GD.N0106.N0428.N0770.N1742.d027779
  rw [(_root_.GD.N0106.N0428.N0770.N1724.d024328 mu sigma zeta a t hsigma hzeta).2, hkt]



theorem d027782 (mu sigma zeta a t : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    IntegrableOn (fun x => _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      _root_.GD.N0232.N0720.N1436.d013218 volume := by
  have hmem := _root_.GD.N0106.N0428.N0770.N1724.d024320 mu sigma zeta hsigma hzeta (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t)
    (_root_.GD.N0106.N0428.N0770.N1725.d024167 a t) (B := 1 + |a| + 7 * |t|) (by positivity)
    (_root_.GD.N0106.N0428.N0770.N1724.d024327 a t)
  have hsq := hmem.integrable_sq
  have hint : Integrable (fun w => _root_.GD.N0107.d009090 2 2 w ^ 2 *
      (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) := by
    simpa only [mul_pow] using hsq
  exact (_root_.GD.N0106.N0428.N0770.N1722.d024344 mu sigma zeta hsigma hzeta
    (fun x => (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2) (_root_.GD.N0106.N0428.N0770.N1742.d027780 a t sigma zeta)).mp
    hint



theorem d027783 (a t s : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - s) ^ 2
      - _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - s) ^ 2 =
        t * (2 * (x.1 - s) * _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x + t * (_root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2)) := by
  have hQJ := _root_.GD.N0106.N0428.N0770.N1726.d024385 x
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024154
  linear_combination (2 * t * a * _root_.GD.N0106.N0428.N0770.N1725.d024170 s x) * hQJ

theorem d027784 (a s : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a _root_.GD.N0106.N0428.N0770.N1725.d024119 x - s) ^ 2
      - _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - s) ^ 2 = _root_.GD.N0106.N0428.N0770.N1725.d024119 * _root_.GD.N0106.N0428.N0770.N1741.d027734 s x := by
  simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027734] using _root_.GD.N0106.N0428.N0770.N1742.d027783 a _root_.GD.N0106.N0428.N0770.N1725.d024119 s x

theorem d027785 (a t s : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - s) ^ 2
      - _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - s) ^ 2 = t * _root_.GD.N0106.N0428.N0770.N1741.d027773 s t x := by
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027783, _root_.GD.N0106.N0428.N0770.N1741.d027774]


theorem d027786 (s : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119 x - s) ^ 2
      - _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 x - s) ^ 2 = _root_.GD.N0106.N0428.N0770.N1725.d024119 * _root_.GD.N0106.N0428.N0770.N1741.d027734 s x :=
  _root_.GD.N0106.N0428.N0770.N1742.d027784 _root_.GD.N0106.N0428.N0770.N1725.d024117 s x




theorem d027787 {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (a t : ℝ)
    (ht : 0 ≤ t) (hstep : t ≤ _root_.GD.N0106.N0428.N0770.N1725.d024119) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - s) ^ 2
      - _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - s) ^ 2 ≤ t * _root_.GD.N0106.N0428.N0770.N1741.d027734 s x := by
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027783]
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027734
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_right hstep (_root_.GD.N0106.N0428.N0770.N1741.d027739 hs x)) _) ht



theorem d027788 (mu sigma zeta a : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a _root_.GD.N0106.N0428.N0770.N1725.d024119 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a 0 =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024119 * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p) := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta a _root_.GD.N0106.N0428.N0770.N1725.d024119 hsigma hzeta
  have h0 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta a 0 hsigma hzeta
  have hdiff : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a _root_.GD.N0106.N0428.N0770.N1725.d024119 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      - (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      = _root_.GD.N0106.N0428.N0770.N1725.d024119 * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p := by
    rw [← integral_sub h1 h0]
    have hpt : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a _root_.GD.N0106.N0428.N0770.N1725.d024119 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
          - _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2))
        = ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024119 * _root_.GD.N0106.N0428.N0770.N1741.d027734 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun x => _root_.GD.N0106.N0428.N0770.N1742.d027784 a (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x)
    rw [hpt, integral_const_mul,
      setIntegral_eq_integral_of_forall_compl_eq_zero (s := _root_.GD.N0232.N0720.N1436.d013218)
        (fun x hx => _root_.GD.N0106.N0428.N0770.N1741.d027738 (q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) hx)]
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta a _root_.GD.N0106.N0428.N0770.N1725.d024119 hsigma hzeta,
    _root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta a 0 hsigma hzeta]
  linear_combination _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * hdiff

theorem d027789 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024119 * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p) :=
  _root_.GD.N0106.N0428.N0770.N1742.d027788 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 hsigma hzeta



theorem d027790 (mu sigma zeta a t : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a t - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a 0 =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (t * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027773 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) t p) := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta a t hsigma hzeta
  have h0 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta a 0 hsigma hzeta
  have hdiff : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      - (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      = t * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027773 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) t p := by
    rw [← integral_sub h1 h0]
    have hpt : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
          - _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 a 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2))
        = ∫ x in _root_.GD.N0232.N0720.N1436.d013218, t * _root_.GD.N0106.N0428.N0770.N1741.d027773 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) t x :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun x => _root_.GD.N0106.N0428.N0770.N1742.d027785 a t (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x)
    rw [hpt, integral_const_mul,
      setIntegral_eq_integral_of_forall_compl_eq_zero (s := _root_.GD.N0232.N0720.N1436.d013218)
        (fun x hx => _root_.GD.N0106.N0428.N0770.N1741.d027775 (q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) (t := t) hx)]
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta a t hsigma hzeta,
    _root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta a 0 hsigma hzeta]
  linear_combination _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * hdiff



theorem d027791 (mu sigma zeta a t : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (ht : 0 ≤ t) (hstep : t ≤ _root_.GD.N0106.N0428.N0770.N1725.d024119) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a t - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a 0 ≤
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (t * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p) := by
  have hs0 : 0 < _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta :=
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have hs1 : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta < 1 :=
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hq : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, hs1.le⟩
  have h1 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta a t hsigma hzeta
  have h0 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta a 0 hsigma hzeta
  have hupper : IntegrableOn (fun x => t * _root_.GD.N0106.N0428.N0770.N1741.d027734 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x)
      _root_.GD.N0232.N0720.N1436.d013218 volume := (_root_.GD.N0106.N0428.N0770.N1741.d027744 hq).integrableOn.const_mul t
  have hle := integral_mono (h1.sub h0) hupper (_root_.GD.N0106.N0428.N0770.N1742.d027787 hq a t ht hstep)
  simp only [Pi.sub_apply] at hle
  rw [integral_sub h1 h0, integral_const_mul,
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := _root_.GD.N0232.N0720.N1436.d013218)
      (fun x hx => _root_.GD.N0106.N0428.N0770.N1741.d027738 (q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) hx)] at hle
  have hscaled := mul_le_mul_of_nonneg_left hle (_root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta).le
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta a t hsigma hzeta,
    _root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta a 0 hsigma hzeta]
  nlinarith only [hscaled]



theorem d027792 (mu sigma zeta a t : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) (ht : 0 < t) (hstep : t ≤ _root_.GD.N0106.N0428.N0770.N1725.d024119) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a t < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a 0 := by
  have hs0 : 0 < _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta :=
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have hs1 : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta < 1 :=
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hneg := _root_.GD.N0106.N0428.N0770.N1741.d027771 (q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ⟨hs0.le, hs1.le⟩
  have hK := _root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta
  have hdiff := _root_.GD.N0106.N0428.N0770.N1742.d027791 mu sigma zeta a t hsigma hzeta ht.le hstep
  have hlt : _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (t * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p) < 0 :=
    mul_neg_of_pos_of_neg hK (mul_neg_of_pos_of_neg ht hneg)
  linarith [hdiff, hlt]

theorem d027793 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119 < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 :=
  _root_.GD.N0106.N0428.N0770.N1742.d027792 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119 hsigma hzeta _root_.GD.N0106.N0428.N0770.N1725.d024123 le_rfl


theorem d027794 (mu sigma zeta a t : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) (ht : 0 < t) (hstep : t ≤ _root_.GD.N0106.N0428.N0770.N1725.d024119) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a t (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a 0 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) :=
  _root_.GD.N0106.N0428.N0770.N1742.d027792 mu sigma zeta a t hsigma hzeta ht hstep



theorem d027795 (mu sigma zeta a t : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) (ht : 0 < t) (hstep : t < 9 / 40000) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a t (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a 0 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) := by
  change _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a t < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta a 0
  have hs0 : 0 < _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta :=
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have hs1 : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta < 1 :=
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hneg := _root_.GD.N0106.N0428.N0770.N1741.d027778 (q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ⟨hs0.le, hs1.le⟩ hstep
  have hdiff := _root_.GD.N0106.N0428.N0770.N1742.d027790 mu sigma zeta a t hsigma hzeta
  have hlt : _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (t * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027773 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) t p) < 0 :=
    mul_neg_of_pos_of_neg (_root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta)
      (mul_neg_of_pos_of_neg ht hneg)
  linarith only [hdiff, hlt]



theorem d027796 (mu sigma zeta a t : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) (ht : 0 < t) (hstep : t ≤ 1 / 5000) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a t (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a 0 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) :=
  _root_.GD.N0106.N0428.N0770.N1742.d027795 mu sigma zeta a t hsigma hzeta ht (by linarith)




theorem d027797 (mu sigma zeta t : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) (ht : 0 < t) (hstep : t < 9 / 40000) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 0 t (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024157 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) :=
  _root_.GD.N0106.N0428.N0770.N1742.d027795 mu sigma zeta 0 t hsigma hzeta ht hstep





theorem d027798 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024159 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024158 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) :=
  _root_.GD.N0106.N0428.N0770.N1742.d027793 mu sigma zeta hsigma hzeta

end
end GD.N0106.N0428.N0770.N1742

#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027781
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027782
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027789
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027788
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027791
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027794
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027790
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027795
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027796
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027797
#print axioms _root_.GD.N0106.N0428.N0770.N1742.d027798
