import GD.Module1865
import GD.Module1171
import GD.Module0940
import GD.Module0900
import GD.Module1208

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0082.N0335

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1369 _root_.GD.N0232.N0720.N1219
open _root_.GD.N0076.N0313
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0230.N0602
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1504

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030707 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) 1 then
    (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn t ht) p).toReal /
      _root_.GD.N0076.N0313.d030565 m n hm hn (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn t ht)
  else 0

theorem d030708 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0335.d030707 m n hm hn p t =
      (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn t ht) p).toReal /
        _root_.GD.N0076.N0313.d030565 m n hm hn (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn t ht) := by
  simp only [_root_.GD.N0082.N0335.d030707, dif_pos ht]

theorem d030709 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (t : ℝ) :
    0 ≤ _root_.GD.N0082.N0335.d030707 m n hm hn p t := by
  unfold _root_.GD.N0082.N0335.d030707
  split_ifs with ht
  · exact div_nonneg ENNReal.toReal_nonneg (_root_.GD.N0076.N0313.d030566 m n hm hn _).le
  · exact le_rfl

def d030710 (u : ℝ) : ℝ := max 0 (min 1 u)

theorem d030711 (u : ℝ) : _root_.GD.N0082.N0335.d030710 u ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem d030712 {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : _root_.GD.N0082.N0335.d030710 u = u := by
  rw [_root_.GD.N0082.N0335.d030710, min_eq_right hu.2, max_eq_right hu.1]

theorem d030713 : Measurable _root_.GD.N0082.N0335.d030710 := by unfold _root_.GD.N0082.N0335.d030710; fun_prop

def d030714 (u : ℝ) : ℝ := 3 * _root_.GD.N0082.N0335.d030710 u ^ 2 - 2 * _root_.GD.N0082.N0335.d030710 u ^ 3

theorem d030715 (u : ℝ) : _root_.GD.N0082.N0335.d030714 u ∈ Icc (0 : ℝ) 1 := by
  have h := _root_.GD.N0082.N0335.d030711 u
  constructor
  · have hp := mul_nonneg (sq_nonneg (_root_.GD.N0082.N0335.d030710 u)) (show 0 ≤ 3 - 2 * _root_.GD.N0082.N0335.d030710 u by linarith [h.2])
    dsimp only [_root_.GD.N0082.N0335.d030714]
    nlinarith
  · have hp := mul_nonneg (sq_nonneg (1 - _root_.GD.N0082.N0335.d030710 u)) (show 0 ≤ 1 + 2 * _root_.GD.N0082.N0335.d030710 u by linarith [h.1])
    dsimp only [_root_.GD.N0082.N0335.d030714]
    nlinarith

theorem d030716 {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0082.N0335.d030714 u = 3 * u ^ 2 - 2 * u ^ 3 := by
  rw [_root_.GD.N0082.N0335.d030714, _root_.GD.N0082.N0335.d030712 hu]

theorem d030717 : Measurable _root_.GD.N0082.N0335.d030714 := by
  unfold _root_.GD.N0082.N0335.d030714
  exact ((_root_.GD.N0082.N0335.d030713.pow_const 2).const_mul 3).sub
    ((_root_.GD.N0082.N0335.d030713.pow_const 3).const_mul 2)

theorem d030718 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) : ContinuousOn (_root_.GD.N0082.N0335.d030707 m n hm hn p) (Ioo 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun t : Ioo (0 : ℝ) 1 => _root_.GD.N0082.N0335.d030707 m n hm hn p t)
  have hc := (_root_.GD.N0232.N0720.N1369.d018805 p hp).comp
    (_root_.GD.N0232.N0720.N1369.d018802 m n hm hn)
  have hb := (_root_.GD.N0232.N0720.N1369.d018805
    (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) (_root_.GD.N0232.N0720.N1369.d018803 m n hm hn)).comp
    (_root_.GD.N0232.N0720.N1369.d018802 m n hm hn)
  have hdiv := hc.div hb (fun t => (_root_.GD.N0076.N0313.d030566 m n hm hn
    (_root_.GD.N0232.N0720.N1369.d018801 m n hm hn t)).ne')
  convert hdiv using 1
  funext t
  exact _root_.GD.N0082.N0335.d030708 m n hm hn p t t.property

theorem d030719 : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) := by
  intro θ
  rw [_root_.GD.N0232.N0720.N1080.d014185]
  exact ENNReal.ofReal_ne_top

def d030720 : ℝ → ℝ := _root_.GD.N0082.N0335.d030707 m n hm hn (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)

theorem d030721 :
    ContinuousOn (_root_.GD.N0082.N0335.d030720 m n hm hn) (Ioo 0 1) :=
  _root_.GD.N0082.N0335.d030718 m n hm hn _ (_root_.GD.N0082.N0335.d030719 m n hm hn)

theorem d030722 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0335.d030720 m n hm hn t < 1 := by
  rw [_root_.GD.N0082.N0335.d030720, _root_.GD.N0082.N0335.d030708 m n hm hn _ t ht]
  rw [div_lt_one (_root_.GD.N0076.N0313.d030566 m n hm hn _)]
  exact (ENNReal.toReal_lt_toReal (_root_.GD.N0082.N0335.d030719 m n hm hn _)
    (_root_.GD.N0232.N0720.N1369.d018803 m n hm hn _)).mpr
    (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn _)

theorem d030723
    {α β t : ℝ} (hα : 0 < α) (hβ : 0 < β) (ht0 : 0 < t) (ht1 : t < 1)
    (f : ℝ → ℝ) (hf : Measurable f) :
    _root_.GD.N0120.d008809 α β t (fun x : ℝ × ℝ => f x.1) =
      ∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 α β t) u) ∂ProbabilityTheory.betaMeasure α β := by
  rw [_root_.GD.N0232.N0720.N1091.d012797 hα hβ f hf]
  calc
    _ = ∫ q, f (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 α β t) (_root_.GD.N0232.N0720.N1091.d012760 α β q))
        ∂_root_.GD.N0232.N0720.N1091.d012754 α β := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0232.N0720.N1091.d012782 hα hβ ht0 ht1] with q hq
      rw [hq]
    _ = ∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 α β t) u)
        ∂(_root_.GD.N0232.N0720.N1091.d012754 α β).map (_root_.GD.N0232.N0720.N1091.d012760 α β) := by
      symm
      exact integral_map (_root_.GD.N0232.N0720.N1091.d012770 α β).aemeasurable
        (hf.comp (_root_.GD.N0232.N0720.N1091.d012771 _)).aestronglyMeasurable
    _ = _ := by rw [_root_.GD.N0232.N0720.N1504.d013979 hα hβ]

def d030724 (H : ℝ → ℝ) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0232.N0720.N1425.d014719 m n (fun x => H x.1)

theorem d030725 (H : ℝ → ℝ) (hH : Measurable H) :
    Measurable (_root_.GD.N0082.N0335.d030724 m n H) := by
  have heq : _root_.GD.N0082.N0335.d030724 m n H = fun ω =>
      _root_.GD.N0107.d009084 ω.2 + _root_.GD.N0107.d009090 m n ω *
        H (_root_.GD.N0107.d009091 m n (_root_.GD.N0107.d009085 ω.1) (_root_.GD.N0107.d009085 ω.2)) := by
    funext ω
    exact _root_.GD.N0232.N0720.N1425.d014720 m n (fun x => H x.1) ω
  rw [heq]
  fun_prop

theorem d030726 (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0107.d009091 m n (_root_.GD.N0107.d009085 ω.1) (_root_.GD.N0107.d009085 ω.2)
      ∈ Icc (0 : ℝ) 1 := by
  have hx : 0 ≤ _root_.GD.N0107.d009085 ω.1 := by
    unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
    positivity
  have hy : 0 ≤ _root_.GD.N0107.d009085 ω.2 := by
    unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
    positivity
  unfold _root_.GD.N0107.d009091
  constructor
  · positivity
  · apply div_le_one_of_le₀
    · linarith [div_nonneg hx (show (0 : ℝ) ≤ m by positivity)]
    · positivity

theorem d030727 : _root_.GD.N0082.N0335.d030724 m n _root_.GD.N0082.N0335.d030710 = _root_.GD.N0232.N0720.N1080.d014175 m n := by
  funext ω
  rw [_root_.GD.N0082.N0335.d030724, _root_.GD.N0232.N0720.N1425.d014720,
    _root_.GD.N0082.N0335.d030712 (_root_.GD.N0082.N0335.d030726 m n ω)]
  unfold _root_.GD.N0232.N0720.N1080.d014175 _root_.GD.N0107.d012733
  ring

include hm hn in
theorem d030728 (H : ℝ → ℝ) (hH : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (fun ω => _root_.GD.N0082.N0335.d030724 m n H ω - θ.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) :=
  _root_.GD.N0232.N0720.N1287.d019517
    m n hm hn θ (fun x => H x.1) (hH.comp measurable_fst) (fun x => hHI x.1)

include hm hn in
theorem d030729 (H : ℝ → ℝ) (hH : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0082.N0335.d030724 m n H ∈ _root_.GD.N0232.N0720.N1256.d015551 m n := by
  refine ⟨_root_.GD.N0082.N0335.d030725 m n H hH, fun θ => ?_⟩
  exact (lintegral_ofReal_ne_top_iff_integrable
    (_root_.GD.N0082.N0335.d030728 m n hm hn H hH hHI θ).integrable_sq.aestronglyMeasurable
    (ae_of_all _ fun _ => sq_nonneg _)).mpr
      (_root_.GD.N0082.N0335.d030728 m n hm hn H hH hHI θ).integrable_sq

include hm hn in
theorem d030730 (H : ℝ → ℝ) (hH : Measurable H)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ u, |H u| ≤ B)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ) (fun ω => _root_.GD.N0082.N0335.d030724 m n H ω - μ) =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
        (_root_.GD.N0107.d012732 m n μ (_root_.GD.N0107.d009046 m n σ τ)) +
      _root_.GD.N0107.d009045 m n σ τ *
        ∫ u, (H (_root_.GD.N0232.N0720.N1091.d012763
          (_root_.GD.N0232.N0720.N1091.d012762 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)
            (_root_.GD.N0107.d009046 m n σ τ)) u) -
              _root_.GD.N0107.d009046 m n σ τ) ^ 2
          ∂ProbabilityTheory.betaMeasure (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) := by
  rw [_root_.GD.N0082.N0335.d030724, _root_.GD.N0232.N0720.N1425.d014726
    m n hm hn μ σ τ hσ hτ (fun x => H x.1) (hH.comp measurable_fst) hB
      (fun x => hbound x.1)]
  have ht0 := _root_.GD.N0107.d009050
    (by omega : 0 < m) (by omega : 0 < n) hσ hτ
  have ht1 := _root_.GD.N0107.d009051
    (by omega : 0 < m) (by omega : 0 < n) hσ hτ
  rw [← _root_.GD.N0232.N0720.N1425.d014723 hm hn ht0 ht1
    (fun x => (H x.1 - _root_.GD.N0107.d009046 m n σ τ) ^ 2)
    (by fun_prop)]
  rw [_root_.GD.N0082.N0335.d030723 (_root_.GD.N0232.N0720.N1436.d013211 hm)
    (_root_.GD.N0232.N0720.N1436.d013212 hn) ht0 ht1
      (fun u => (H u - _root_.GD.N0107.d009046 m n σ τ) ^ 2)
      (by fun_prop)]

end
end GD.N0082.N0335

#print axioms _root_.GD.N0082.N0335.d030718
#print axioms _root_.GD.N0082.N0335.d030709
#print axioms _root_.GD.N0082.N0335.d030715
#print axioms _root_.GD.N0082.N0335.d030716
#print axioms _root_.GD.N0082.N0335.d030727
#print axioms _root_.GD.N0082.N0335.d030721
#print axioms _root_.GD.N0082.N0335.d030722
#print axioms _root_.GD.N0082.N0335.d030723
#print axioms _root_.GD.N0082.N0335.d030725
#print axioms _root_.GD.N0082.N0335.d030728
#print axioms _root_.GD.N0082.N0335.d030729
#print axioms _root_.GD.N0082.N0335.d030730
