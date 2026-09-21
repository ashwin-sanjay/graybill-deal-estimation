import GD.Module1677
import GD.Module1435
import GD.Module0813

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0091
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0963
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973

variable {k : ℕ}



theorem d028705 (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hd : Measurable d)
    {c : ℝ} (hc : 0 ≤ c)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤
      ENNReal.ofReal c * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ ENNReal.ofReal (c * (k : ℝ)) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  have hgd := _root_.GD.N0070.d028368
    (by omega) sizes hn
  apply (_root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd).trans
  apply iSup_le
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) hn0
    (c * (k : ℝ)) (by positivity) θ d).mpr
  have hpoint : _root_.GD.N0232.N0719.N0962.d012186 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤
      ENNReal.ofReal (k : ℝ) :=
    (le_iSup (fun η => _root_.GD.N0232.N0719.N0962.d012186 k sizes η (_root_.GD.N0232.N0719.N0900.d009111 k sizes)) θ).trans hgd
  have hb := (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) hn0 (k : ℝ)
    (by positivity) θ _).mp hpoint
  calc
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤
        ENNReal.ofReal c * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) := hcap θ
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal ((k : ℝ) * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) :=
      mul_le_mul_right hb _
    _ = ENNReal.ofReal (c * (k : ℝ) * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
      rw [← ENNReal.ofReal_mul hc, mul_assoc]


theorem d028706 (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ ENNReal.ofReal
      ((_root_.GD.N0232.N0719.N0973.d012377 k sizes hk (fun i => (by have := hn i; omega))).toReal * (k : ℝ)) := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  have hn0 : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  let c := (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn2).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  obtain ⟨d, _, hd, hv, _, _⟩ := _root_.GD.N0232.N0719.N0972.d012350 k sizes hk hn2
  apply _root_.GD.N0091.d028705 sizes hk hn d hd.1 hc
  intro θ
  have hpoint : _root_.GD.N0232.N0719.N0844.d012246 k sizes
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn2) θ d ≤ ENNReal.ofReal c := by
    rw [show ENNReal.ofReal c = _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn2 from
      ENNReal.ofReal_toReal (_root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn2)]
    exact (le_iSup (fun η => _root_.GD.N0232.N0719.N0844.d012246 k sizes
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn2) η d) θ).trans hv.le
  have hr := (_root_.GD.N0232.N0719.N0844.d012250 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn2) (by omega) hn0 c hc θ d).mp hpoint
  have heq : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes θ) :=
    _root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn2 θ
  rw [heq, ← ENNReal.ofReal_mul hc]
  exact hr


theorem d028707 (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    1 / (k : ℝ) <
      (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk (fun i => (by have := hn i; omega))).toReal := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  have h := (_root_.GD.N0066.d022835 sizes hk hn2).trans_le
    (_root_.GD.N0091.d028706 sizes hk hn)
  have hr : (1 : ℝ) < (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn2).toReal * (k : ℝ) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [ENNReal.ofReal_one] using h
  exact (div_lt_iff₀ (by exact_mod_cast (show 0 < k by omega))).mpr hr



theorem d028708 (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk (fun i => (by have := hn i; omega))
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes) < (((1 - 1 / (k : ℝ)) : ℝ) : EReal) := by
  rw [_root_.GD.N0232.N0719.N0973.d012381]
  apply EReal.coe_lt_coe_iff.mpr
  have h := _root_.GD.N0091.d028707 sizes hk hn
  linarith

end
end GD.N0091

#print axioms _root_.GD.N0091.d028705
#print axioms _root_.GD.N0091.d028706
#print axioms _root_.GD.N0091.d028707
#print axioms _root_.GD.N0091.d028708
