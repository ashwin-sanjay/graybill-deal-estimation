import GD.Module1686
import GD.Module1692
import GD.Module1710
import GD.Module0546
import GD.Module1675

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace GD.N0101.N0385
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0230.N0665
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0225.N0538
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0398 _root_.GD.N0101.N0403
open _root_.GD.N0101.N0362 _root_.GD.N0101.N0365 _root_.GD.N0101.N0366
open _root_.GD.N0101.N0361 _root_.GD.N0101.N0364 _root_.GD.N0101.N0392
open _root_.GD.N0220

theorem d028667 (N : ℝ) (hN : 0 < N) :
    _root_.GD.N0101.N0361.d028527 (1/2) (_root_.GD.N0101.N0362.d007947 N) ≤ ENNReal.ofReal (256 / (Real.pi * N)) := by
  change (∫⁻ β, ∫⁻ t, _root_.GD.N0101.N0394.d028505 (1/2)
    (_root_.GD.N0101.N0362.d007947 N) β t ∂(_root_.GD.N0213.N0516.d028411 _root_.GD.N0220.d028624 β)
      ∂(_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624)) ≤ _
  rw [_root_.GD.N0101.N0364.d028665]
  exact _root_.GD.N0101.N0392.d008133 N N hN

theorem d028668 :
    Tendsto (fun N : ℝ => _root_.GD.N0101.N0361.d028527 (1/2) (_root_.GD.N0101.N0362.d007947 N)) atTop (𝓝 0) := by
  have he (N : ℝ) := _root_.GD.N0101.N0364.d028665 N
  change Tendsto (fun N : ℝ => ∫⁻ β, ∫⁻ t,
    _root_.GD.N0101.N0394.d028505 (1/2) (_root_.GD.N0101.N0362.d007947 N) β t
      ∂(_root_.GD.N0213.N0516.d028411 _root_.GD.N0220.d028624 β)
      ∂(_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624)) atTop (𝓝 0)
  simp_rw [he]
  exact _root_.GD.N0101.N0392.d008135 (fun N => N)



theorem d028669
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hshape : _root_.GD.N0232.N0719.N0954.d009355 sizes = (fun _ : Fin 2 => (1/2 : ℝ)))
    (p w : (Fin 2 → ℝ) → Fin 2 → ℝ) (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hpnn : ∀ t i, 0 ≤ p t i)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p))
    (N : ℝ) (hN : 0 < N) :
    (∫⁻ β, ENNReal.ofReal ((_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal -
      (_root_.GD.N0101.N0398.d023335 sizes hn w β).toReal) ∂_root_.GD.N0101.N0365.d028458 (_root_.GD.N0232.N0719.N0954.d009355 sizes) N) ≤
      _root_.GD.N0101.N0361.d028527 (1/2) (_root_.GD.N0101.N0362.d007947 N) := by
  have hpf := _root_.GD.N0225.N0538.d023463 sizes hn p hp hpunit hpnn
  have hfinite : (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn p β
      ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => (1/2 : ℝ)) (_root_.GD.N0101.N0362.d007947 N)) ≠ ⊤ := by
    simpa only [_root_.GD.N0101.N0365.d028458, hshape] using
      _root_.GD.N0101.N0365.d028470 sizes hn hN p hp hpunit hporacle
  have he (β : Fin 2 → ℝ) :
      ENNReal.ofReal ((_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal -
        (_root_.GD.N0101.N0398.d023335 sizes hn w β).toReal) =
      _root_.GD.N0101.N0398.d023335 sizes hn p β - _root_.GD.N0101.N0398.d023335 sizes hn w β := by
    have hbp : _root_.GD.N0101.N0398.d023335 sizes hn p β ≠ ⊤ := hpf.2 _
    have hbw : _root_.GD.N0101.N0398.d023335 sizes hn w β ≠ ⊤ :=
      ne_top_of_le_ne_top hbp (hweak _)
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hbp, ENNReal.ofReal_toReal hbw]
  simp_rw [he]
  change (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn p β - _root_.GD.N0101.N0398.d023335 sizes hn w β
    ∂_root_.GD.N0101.N0403.d028436 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0101.N0362.d007947 N)) ≤ _
  rw [hshape]
  exact _root_.GD.N0101.N0361.d028534 (1/2) (by norm_num) sizes hn hshape
    (_root_.GD.N0101.N0362.d007947 N) (_root_.GD.N0101.N0362.d007949 N) (_root_.GD.N0101.N0362.d007950 N)
    p w hp hw hpunit hwunit hporacle (fun β _ => hweak _) hfinite



theorem d028670
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hshape : _root_.GD.N0232.N0719.N0954.d009355 sizes = (fun _ : Fin 2 => (1/2 : ℝ)))
    (p : (Fin 2 → ℝ) → Fin 2 → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hpnn : ∀ t i, 0 ≤ p t i)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t) :
    ¬ ∃ w : (Fin 2 → ℝ) → Fin 2 → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p) := by
  apply _root_.GD.N0101.N0366.d028474 sizes hn p hp hpunit hpnn
    (fun N => _root_.GD.N0101.N0361.d028527 (1/2) (_root_.GD.N0101.N0362.d007947 N)) _root_.GD.N0101.N0385.d028668
  intro w hw hwunit _ hweak N hN
  exact _root_.GD.N0101.N0385.d028669 sizes hn hshape p w hp hw hpunit hwunit hpnn
    hporacle hweak N (lt_of_lt_of_le zero_lt_one hN)

def d028671 : Fin 2 → ℕ := fun _ => 2

theorem d028672 : ∀ i, 2 ≤ _root_.GD.N0101.N0385.d028671 i := fun _ => le_rfl

theorem d028673 : _root_.GD.N0232.N0719.N0954.d009355 _root_.GD.N0101.N0385.d028671 = (fun _ : Fin 2 => (1/2 : ℝ)) := by
  funext i
  norm_num [_root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0101.N0385.d028671]



theorem d028674 :
    ¬ ∃ w : (Fin 2 → ℝ) → Fin 2 → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0101.N0385.d028671 θ (_root_.GD.N0072.d023291 _root_.GD.N0101.N0385.d028671 w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0101.N0385.d028671 θ (_root_.GD.N0232.N0719.N0900.d009111 2 _root_.GD.N0101.N0385.d028671)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0101.N0385.d028671 θ (_root_.GD.N0072.d023291 _root_.GD.N0101.N0385.d028671 w) <
        _root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0101.N0385.d028671 θ (_root_.GD.N0232.N0719.N0900.d009111 2 _root_.GD.N0101.N0385.d028671) := by
  rw [_root_.GD.N0021.d023315 _root_.GD.N0101.N0385.d028671]
  exact _root_.GD.N0101.N0385.d028670 _root_.GD.N0101.N0385.d028671 _root_.GD.N0101.N0385.d028672 _root_.GD.N0101.N0385.d028673
    _root_.GD.N0021.d023313 _root_.GD.N0225.N0536.d028353
    _root_.GD.N0225.N0536.d028354
    _root_.GD.N0225.N0536.d028355
    (fun t ht => _root_.GD.N0225.N0536.d028356 t ht)

end
end GD.N0101.N0385

#print axioms _root_.GD.N0101.N0385.d028667
#print axioms _root_.GD.N0101.N0385.d028668
#print axioms _root_.GD.N0101.N0385.d028669
#print axioms _root_.GD.N0101.N0385.d028670
#print axioms _root_.GD.N0101.N0385.d028673
#print axioms _root_.GD.N0101.N0385.d028674
