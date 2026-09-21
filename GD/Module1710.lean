import GD.Module1709
import GD.Module1330
import GD.Module1708





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0101.N0364
noncomputable section

open _root_.GD.N0213.N0510
open _root_.GD.N0213.N0508
open _root_.GD.N0213.N0516
open _root_.GD.N0213.N0493
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0101.N0397 _root_.GD.N0101.N0394 _root_.GD.N0101.N0414
open _root_.GD.N0101.N0367 _root_.GD.N0101.N0362 _root_.GD.N0101.N0417
open _root_.GD.N0220
open _root_.GD.N0219 _root_.GD.N0218
open _root_.GD.N0208.N0455

theorem d028657 :
    (_root_.GD.N0101.N0414.d028417 _root_.GD.N0220.d028624).map _root_.GD.N0101.N0397.d028118 = _root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2) :=
  (measurePreserving_piFinTwo (fun _ : Fin 2 => gammaMeasure (1 / 2) (1 / 2))).map_eq

theorem d028658 :
    ∀ᵐ u ∂_root_.GD.N0101.N0414.d028417 _root_.GD.N0220.d028624, ∀ i, 0 < u i := by
  exact _root_.GD.N0232.N0719.N0910.d010287
    (shape := _root_.GD.N0220.d028624) (rate := _root_.GD.N0220.d028624) (fun _ => by norm_num [_root_.GD.N0220.d028624])
    (fun _ => by norm_num [_root_.GD.N0220.d028624])


theorem d028659 (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, f (_root_.GD.N0101.N0367.d028640 u) ∂_root_.GD.N0101.N0414.d028417 _root_.GD.N0220.d028624) =
      ∫⁻ ell : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 ell) * f ell := by
  rw [← _root_.GD.N0101.N0359.d021669 f hf, ← _root_.GD.N0101.N0364.d028657,
    lintegral_map (f := fun z : ℝ × ℝ => f (_root_.GD.N0101.N0359.d021659 z))
      (by fun_prop) _root_.GD.N0101.N0397.d028118.measurable]
  rfl



def d028660 (N s v ell : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0219.d008142 s) *
    ENNReal.ofReal ((Real.exp (s + v) + Real.exp (s - v) * Real.exp ell)⁻¹ *
      (_root_.GD.N0208.N0455.d007937 N s ^ 2 * (_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N (v - ell)) ^ 2))

@[fun_prop] theorem d028661 (N s v : ℝ) :
    Measurable (_root_.GD.N0101.N0364.d028660 N s v) := by
  have hcut := _root_.GD.N0208.N0455.d007938 N
  unfold _root_.GD.N0101.N0364.d028660
  fun_prop

theorem d028662 (N s v : ℝ) (u : Fin 2 → ℝ)
    (hu : ∀ i, 0 < u i) :
    ENNReal.ofReal (_root_.GD.N0219.d008142 s) *
      _root_.GD.N0101.N0394.d028505 (1 / 2) (_root_.GD.N0101.N0362.d007947 N) (_root_.GD.N0220.d028625 (s, v))
        (_root_.GD.N0101.N0414.d028419 (_root_.GD.N0220.d028625 (s, v)) u) =
      _root_.GD.N0101.N0364.d028660 N s v (_root_.GD.N0101.N0367.d028640 u) := by
  unfold _root_.GD.N0101.N0394.d028505
  rw [_root_.GD.N0101.N0367.d028644 N s v u hu,
    _root_.GD.N0101.N0367.d028641 _ _ (_root_.GD.N0220.d028627 _) hu]
  rfl

theorem d028663 (N s v ell : ℝ) :
    _root_.GD.N0101.N0364.d028660 N s v ell * ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 ell) =
      ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v (v - ell)) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N (v - ell)) ^ 2) := by
  let u : Fin 2 → ℝ := ![Real.exp ell, 1]
  have hu : ∀ i, 0 < u i := Fin.forall_fin_two.mpr ⟨Real.exp_pos ell, zero_lt_one⟩
  have hlog : _root_.GD.N0101.N0367.d028640 u = ell := by
    change Real.log (Real.exp ell / 1) = ell
    rw [div_one, Real.log_exp]
  have h := _root_.GD.N0101.N0367.d028645 N s v u hu
  rw [_root_.GD.N0101.N0364.d028662 N s v u hu, hlog] at h
  exact h



theorem d028664 (N s v : ℝ) :
    ENNReal.ofReal (_root_.GD.N0219.d008142 s) *
      (∫⁻ t, _root_.GD.N0101.N0394.d028505 (1 / 2) (_root_.GD.N0101.N0362.d007947 N) (_root_.GD.N0220.d028625 (s, v)) t
        ∂_root_.GD.N0213.N0516.d028411 _root_.GD.N0220.d028624 (_root_.GD.N0220.d028625 (s, v))) =
      ∫⁻ w : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v w) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [_root_.GD.N0101.N0414.d028426 _root_.GD.N0220.d028624 (_root_.GD.N0220.d028625 (s, v))
    (fun _ => by norm_num [_root_.GD.N0220.d028624]) (_root_.GD.N0220.d028627 _) ]
  calc
    _ = ∫⁻ u, _root_.GD.N0101.N0364.d028660 N s v (_root_.GD.N0101.N0367.d028640 u) ∂_root_.GD.N0101.N0414.d028417 _root_.GD.N0220.d028624 := by
      apply lintegral_congr_ae
      filter_upwards [_root_.GD.N0101.N0364.d028658] with u hu
      exact _root_.GD.N0101.N0364.d028662 N s v u hu
    _ = ∫⁻ ell : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 ell) * _root_.GD.N0101.N0364.d028660 N s v ell :=
      _root_.GD.N0101.N0364.d028659 _ (_root_.GD.N0101.N0364.d028661 N s v)
    _ = ∫⁻ ell : ℝ, ENNReal.ofReal
        (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v (v - ell)) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N (v - ell)) ^ 2) := by
      apply lintegral_congr
      intro ell
      rw [mul_comm, _root_.GD.N0101.N0364.d028663]
    _ = _ := lintegral_sub_left_eq_self
      (fun w => ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v w) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) v



theorem d028665 (N : ℝ) :
    (∫⁻ β, ∫⁻ t, _root_.GD.N0101.N0394.d028505 (1 / 2) (_root_.GD.N0101.N0362.d007947 N) β t
      ∂_root_.GD.N0213.N0516.d028411 _root_.GD.N0220.d028624 β ∂_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624) =
      ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
        ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v w) *
          ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2) := by
  rw [_root_.GD.N0101.N0417.d028656 _
    (_root_.GD.N0213.N0508.d028431 _root_.GD.N0220.d028624 _
      (_root_.GD.N0101.N0394.d028511 _ _ (_root_.GD.N0101.N0362.d007949 N)))]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro v
  exact _root_.GD.N0101.N0364.d028664 N s v



theorem d028666 (N : ℝ) :
    (∫⁻ t, ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 _root_.GD.N0220.d028624 (fun i => _root_.GD.N0220.d028624 i * t i)) *
      _root_.GD.N0101.N0394.d028506 (1 / 2) (_root_.GD.N0101.N0362.d007947 N) t ∂_root_.GD.N0213.N0516.d028413 _root_.GD.N0220.d028624 0) =
      ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
        ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v w) *
          ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2) := by
  exact (_root_.GD.N0101.N0394.d028513 (1 / 2) (by norm_num)
    (_root_.GD.N0101.N0362.d007947 N) (_root_.GD.N0101.N0362.d007949 N)).trans
      (_root_.GD.N0101.N0364.d028665 N)

end
end GD.N0101.N0364

#print axioms _root_.GD.N0101.N0364.d028657
#print axioms _root_.GD.N0101.N0364.d028658
#print axioms _root_.GD.N0101.N0364.d028659
#print axioms _root_.GD.N0101.N0364.d028662
#print axioms _root_.GD.N0101.N0364.d028663
#print axioms _root_.GD.N0101.N0364.d028664
#print axioms _root_.GD.N0101.N0364.d028665
#print axioms _root_.GD.N0101.N0364.d028666
