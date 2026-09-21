import GD.Module0924
import GD.Module0940
import GD.Module1176

















open MeasureTheory ProbabilityTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1458

noncomputable section

open _root_.GD.N0232.N0720.N1071
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1459
open _root_.GD.N0232.N0720.N1460
open _root_.GD.N0232.N0720.N1467






def d018936
    (f : ℝ → ℝ → ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  if 0 < x.2 then
    f (Real.sqrt x.2) (1 - x.1) / Real.sqrt x.2
  else 0

@[fun_prop]
theorem d018937
    {f : ℝ → ℝ → ℝ}
    (hf : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2)) :
    Measurable (_root_.GD.N0232.N0720.N1458.d018936 f) := by
  unfold _root_.GD.N0232.N0720.N1458.d018936
  have hset : MeasurableSet {x : _root_.GD.N0232.N0720.N1436.d013217 | 0 < x.2} :=
    measurableSet_lt measurable_const measurable_snd
  apply Measurable.ite hset
  · apply Measurable.div
    · have hmap : Measurable (fun a : _root_.GD.N0232.N0720.N1436.d013217 ↦
          (Real.sqrt a.2, 1 - a.1)) := by fun_prop
      simpa [Function.comp_def] using hf.comp hmap
    · fun_prop
  · exact measurable_const


theorem d018938
    {f : ℝ → ℝ → ℝ} (hf : _root_.GD.N0232.N0720.N1460.d003040 f)
    (z q : ℝ) :
    z * _root_.GD.N0232.N0720.N1458.d018936 f (1 - q, z ^ 2) = f z q := by
  by_cases hz : z = 0
  · subst z
    have hzero := hf 0 q
    simp only [neg_zero] at hzero
    simp [_root_.GD.N0232.N0720.N1458.d018936]
    linarith
  · have hzsq : 0 < z ^ 2 := sq_pos_of_ne_zero hz
    rw [_root_.GD.N0232.N0720.N1458.d018936, if_pos hzsq]
    rw [show 1 - (1 - q) = q by ring]
    rw [Real.sqrt_sq_eq_abs]
    by_cases hzpos : 0 < z
    · rw [abs_of_pos hzpos]
      field_simp
    · have hzneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
      rw [abs_of_neg hzneg]
      rw [hf z q]
      field_simp



theorem d018939
    {s t : ℝ} (hst : s + t ≠ 0) :
    _root_.GD.N0232.N0720.N1437.d002996 s t =
      1 - _root_.GD.N0232.N0720.N1460.d003026 s t := by
  unfold _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1460.d003026
  field_simp
  ring


theorem d018940
    {u v s t : ℝ} (hst : 0 < s + t) :
    _root_.GD.N0232.N0720.N1437.d002997 u v s t = _root_.GD.N0232.N0720.N1460.d003025 u v s t ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1437.d002997 _root_.GD.N0232.N0720.N1460.d003025 _root_.GD.N0232.N0720.N1460.d003024
  rw [div_pow, Real.sq_sqrt hst.le]



theorem d018941
    {f : ℝ → ℝ → ℝ} (hf : _root_.GD.N0232.N0720.N1460.d003040 f)
    {u v s t : ℝ} (hst : 0 < s + t) :
    _root_.GD.N0232.N0720.N1460.d003027 f u v s t =
      _root_.GD.N0232.N0720.N1437.d002998 (fun r w ↦ _root_.GD.N0232.N0720.N1458.d018936 f (r, w))
        u v s t := by
  let a := _root_.GD.N0232.N0720.N1460.d003024 s t
  let z := _root_.GD.N0232.N0720.N1460.d003025 u v s t
  let q := _root_.GD.N0232.N0720.N1460.d003026 s t
  have ha : 0 < a := _root_.GD.N0232.N0720.N1460.d003034 hst
  have hcontrast : u - v = a * z := by
    have h := _root_.GD.N0232.N0720.N1460.d003037
      (u := u) (v := v) (s := s) (t := t) ha.ne'
    dsimp only [a, z] at *
    linarith
  have hfrac : _root_.GD.N0232.N0720.N1437.d002996 s t = 1 - q := by
    exact _root_.GD.N0232.N0720.N1458.d018939 hst.ne'
  have hratio : _root_.GD.N0232.N0720.N1437.d002997 u v s t = z ^ 2 := by
    exact _root_.GD.N0232.N0720.N1458.d018940 hst
  unfold _root_.GD.N0232.N0720.N1460.d003027 _root_.GD.N0232.N0720.N1437.d002998
  dsimp only [a, z, q] at hcontrast hfrac hratio ⊢
  rw [hfrac, hratio, hcontrast]
  rw [← _root_.GD.N0232.N0720.N1458.d018938 hf]
  ring




def d018942
    (m n : ℕ) (f : ℝ → ℝ → ℝ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0232.N0720.N1460.d003027 f
    (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
    (_root_.GD.N0232.N0720.N1084.d014252 m n omega)
    (_root_.GD.N0232.N0720.N1084.d014253 m n omega)

@[fun_prop]
theorem d018943
    (m n : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2)) :
    Measurable (_root_.GD.N0232.N0720.N1458.d018942 m n f) := by
  unfold _root_.GD.N0232.N0720.N1458.d018942 _root_.GD.N0232.N0720.N1460.d003027 _root_.GD.N0232.N0720.N1460.d003025
    _root_.GD.N0232.N0720.N1460.d003024 _root_.GD.N0232.N0720.N1460.d003026
    _root_.GD.N0232.N0720.N1084.d014252
    _root_.GD.N0232.N0720.N1084.d014253
  fun_prop




def d018944
    (f : ℝ → ℝ → ℝ) (oracleFraction : ℝ)
    (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (f (Real.sqrt x.2) (1 - x.1) -
      oracleFraction * Real.sqrt x.2) ^ 2 / x.2

@[fun_prop]
theorem d018945
    {f : ℝ → ℝ → ℝ}
    (hf : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2))
    (oracleFraction : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1458.d018944 f oracleFraction) := by
  unfold _root_.GD.N0232.N0720.N1458.d018944
  fun_prop



theorem d018946
    (f : ℝ → ℝ → ℝ) (oracleFraction : ℝ)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    (_root_.GD.N0232.N0720.N1458.d018936 f x - oracleFraction) ^ 2 =
      _root_.GD.N0232.N0720.N1458.d018944 f oracleFraction x := by
  have hs : 0 < x.2 := hx.2
  have hsqrt : 0 < Real.sqrt x.2 := Real.sqrt_pos.2 hs
  unfold _root_.GD.N0232.N0720.N1458.d018936 _root_.GD.N0232.N0720.N1458.d018944
  rw [if_pos hs]
  calc
    (f (√x.2) (1 - x.1) / √x.2 - oracleFraction) ^ 2 =
        (f (√x.2) (1 - x.1) - oracleFraction * √x.2) ^ 2 /
          (√x.2) ^ 2 := by
      field_simp [hsqrt.ne']
    _ = (f (√x.2) (1 - x.1) - oracleFraction * √x.2) ^ 2 /
          x.2 := by rw [Real.sq_sqrt hs.le]


theorem d018947
    (m n : ℕ) (oracleFraction : ℝ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n oracleFraction,
      x ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  apply (_root_.GD.N0232.N0720.N1436.d013290
    m n oracleFraction).ae_le
  unfold _root_.GD.N0232.N0720.N1436.d013288
  exact ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219






theorem d018948
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (f : ℝ → ℝ → ℝ)
    (hfMeasurable : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2))
    (hfOdd : _root_.GD.N0232.N0720.N1460.d003040 f)
    (hfinite : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1458.d018942 m n f omega - mu)
      2 (_root_.GD.N0107.d009030 m n mu sigma tau)) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega ↦ _root_.GD.N0232.N0720.N1458.d018942 m n f omega - mu) =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0107.d012732 m n mu (_root_.GD.N0107.d009046 m n sigma tau)) +
        _root_.GD.N0107.d009045 m n sigma tau *
          ∫ x, _root_.GD.N0232.N0720.N1458.d018944 f (_root_.GD.N0107.d009046 m n sigma tau) x
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n (_root_.GD.N0107.d009046 m n sigma tau) := by
  let g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ := _root_.GD.N0232.N0720.N1458.d018936 f
  let theta : _root_.GD.N0232.N0720.N1080.d014168 :=
    { location := mu
      scale₁ := sigma
      scale₂ := tau
      scale₁_pos := hsigma
      scale₂_pos := htau }
  have hpositiveRef := _root_.GD.N0232.N0720.N1459.d018933 m n hm hn
  have hpositive :
      ∀ᵐ omega ∂_root_.GD.N0107.d009030 m n mu sigma tau,
        0 < _root_.GD.N0232.N0720.N1084.d014252 m n omega +
          _root_.GD.N0232.N0720.N1084.d014253 m n omega := by
    have htransport := (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
      hpositiveRef
    change ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta,
      0 < _root_.GD.N0232.N0720.N1084.d014252 m n omega +
        _root_.GD.N0232.N0720.N1084.d014253 m n omega
    filter_upwards [htransport] with omega homega
    simpa [_root_.GD.N0232.N0720.N1467.d012547,
      _root_.GD.N0232.N0720.N1467.d012548,
      _root_.GD.N0232.N0720.N1084.d014252,
      _root_.GD.N0232.N0720.N1084.d014253] using homega
  have heq :
      _root_.GD.N0232.N0720.N1458.d018942 m n f =ᵐ[_root_.GD.N0107.d009030 m n mu sigma tau]
        _root_.GD.N0232.N0720.N1425.d014719 m n g := by
    filter_upwards [hpositive] with omega homega
    exact _root_.GD.N0232.N0720.N1458.d018941
      hfOdd homega
  have hprojectiveFinite : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu)
      2 (_root_.GD.N0107.d009030 m n mu sigma tau) := by
    apply (memLp_congr_ae ?_).2 hfinite
    exact heq.fun_comp (fun y ↦ y - mu) |>.symm
  have hgMeasurable : Measurable g :=
    _root_.GD.N0232.N0720.N1458.d018937 hfMeasurable
  have hcarrier :=
    _root_.GD.N0232.N0720.N1425.d014722
      m n hm hn mu sigma tau hsigma htau g hprojectiveFinite
  have hrisk :=
    _root_.GD.N0232.N0720.N1425.d014725
      m n hm hn mu sigma tau hsigma htau g hgMeasurable hcarrier
  have hriskCongr :
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1458.d018942 m n f omega - mu) =
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu) := by
    unfold _root_.GD.N0141.d006684
    apply integral_congr_ae
    exact (heq.fun_comp (fun y ↦ (y - mu) ^ 2))
  have hintegral :
      (∫ x, (g x - _root_.GD.N0107.d009046 m n sigma tau) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n (_root_.GD.N0107.d009046 m n sigma tau)) =
        ∫ x, _root_.GD.N0232.N0720.N1458.d018944 f (_root_.GD.N0107.d009046 m n sigma tau) x
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n (_root_.GD.N0107.d009046 m n sigma tau) := by
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0232.N0720.N1458.d018947
      m n (_root_.GD.N0107.d009046 m n sigma tau)] with x hx
    exact _root_.GD.N0232.N0720.N1458.d018946
      f (_root_.GD.N0107.d009046 m n sigma tau) hx
  rw [hriskCongr, hrisk, hintegral]





def d018949 (rho : ℝ) : ℝ :=
  rho ^ 2 / (1 + rho ^ 2)




theorem d018950
    (rho : ℝ) (hrho : 0 < rho)
    (f : ℝ → ℝ → ℝ)
    (hfMeasurable : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2))
    (hfOdd : _root_.GD.N0232.N0720.N1460.d003040 f)
    (hfinite : MemLp
      (_root_.GD.N0232.N0720.N1458.d018942 2 2 f)
      2 (_root_.GD.N0107.d009030 2 2 0 1 rho)) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 0 1 rho)
        (_root_.GD.N0232.N0720.N1458.d018942 2 2 f) =
      rho ^ 2 / (2 * (1 + rho ^ 2)) +
        ((1 + rho ^ 2) / 2) *
          ∫ x, _root_.GD.N0232.N0720.N1458.d018944 f (_root_.GD.N0232.N0720.N1458.d018949 rho) x
            ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0232.N0720.N1458.d018949 rho) := by
  have hrisk :=
    _root_.GD.N0232.N0720.N1458.d018948
      2 2 (by norm_num) (by norm_num) 0 1 rho one_pos hrho
      f hfMeasurable hfOdd (by simpa using hfinite)
  let theta : _root_.GD.N0232.N0720.N1080.d014168 :=
    { location := 0
      scale₁ := 1
      scale₂ := rho
      scale₁_pos := one_pos
      scale₂_pos := hrho }
  have horacle := _root_.GD.N0232.N0720.N1071.d014426
    2 2 (by norm_num) (by norm_num) theta
  have hfraction : _root_.GD.N0107.d009046 2 2 1 rho =
      _root_.GD.N0232.N0720.N1458.d018949 rho := by
    unfold _root_.GD.N0107.d009046 _root_.GD.N0232.N0720.N1458.d018949
      _root_.GD.N0107.d009045
      _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
    norm_num
    field_simp
  have htotal : _root_.GD.N0107.d009045 2 2 1 rho = (1 + rho ^ 2) / 2 := by
    norm_num [_root_.GD.N0107.d009045, _root_.GD.N0107.d009043, _root_.GD.N0107.d009044]
    ring
  have horacle' :
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 0 1 rho)
          (_root_.GD.N0107.d012732 2 2 0 (_root_.GD.N0107.d009046 2 2 1 rho)) =
        rho ^ 2 / (2 * (1 + rho ^ 2)) := by
    have horacleRaw :
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 0 1 rho)
            (_root_.GD.N0107.d012732 2 2 0 (_root_.GD.N0107.d009046 2 2 1 rho)) =
          (1 + rho ^ 2) / 2 *
            (rho ^ 2 / (1 + rho ^ 2) *
              (1 - rho ^ 2 / (1 + rho ^ 2))) := by
      simpa [_root_.GD.N0232.N0720.N1080.d014171, theta, _root_.GD.N0232.N0720.N1067.d014408, hfraction,
        htotal, _root_.GD.N0232.N0720.N1442.d013866, _root_.GD.N0232.N0720.N1458.d018949] using horacle
    rw [horacleRaw]
    have hden : 1 + rho ^ 2 ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [hfraction] at horacle'
  rw [hfraction, htotal, horacle'] at hrisk
  simpa only [sub_zero] using hrisk

end

end N1458
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1458.d018941
#print axioms _root_.GD.N0232.N0720.N1458.d018948
#print axioms _root_.GD.N0232.N0720.N1458.d018950
