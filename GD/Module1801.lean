import GD.Module1800
import GD.Module1461
import GD.Module1443

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0390
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0045 _root_.GD.N0101.N0393

def d029964 : _root_.GD.N0232.N0720.N1441.d013676 := ⟨1 / 4, by norm_num, by norm_num⟩
def d029965 : _root_.GD.N0232.N0720.N1441.d013676 := ⟨3 / 4, by norm_num, by norm_num⟩


def d029966 (m n : ℕ) : ℝ :=
  ∫ z, min (_root_.GD.N0232.N0720.N1436.d013273 m n _root_.GD.N0101.N0390.d029964.1 z)
    (_root_.GD.N0232.N0720.N1436.d013273 m n _root_.GD.N0101.N0390.d029965.1 z) ∂_root_.GD.N0232.N0720.N1436.d013288

theorem d029967 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    (∫ z, _root_.GD.N0232.N0720.N1436.d013273 m n t.1 z ∂_root_.GD.N0232.N0720.N1436.d013288) = 1 := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1441.d013678 m n t) :=
    _root_.GD.N0232.N0720.N1434.d013564 hm hn t.2.1 t.2.2
  calc
    _ = ∫ _, (1 : ℝ) ∂_root_.GD.N0232.N0720.N1441.d013678 m n t := by
      simpa only [mul_one] using
        (_root_.GD.N0045.d021923 m n hm hn t (fun _ => (1 : ℝ))).symm
    _ = 1 := by simp

theorem d029968 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1436.d013288 ≠ 0 := by
  intro h
  have hh := _root_.GD.N0101.N0390.d029967 m n hm hn _root_.GD.N0101.N0390.d029964
  simp only [h, integral_zero_measure] at hh
  norm_num at hh

theorem d029969 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    0 < _root_.GD.N0101.N0390.d029966 m n := by
  exact _root_.GD.N0101.N0393.d029961 (_root_.GD.N0101.N0390.d029968 m n hm hn)
    (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029964) (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029965)
    (_root_.GD.N0045.d021922 m n hm hn _root_.GD.N0101.N0390.d029964) (_root_.GD.N0045.d021922 m n hm hn _root_.GD.N0101.N0390.d029965)

theorem d029970 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0101.N0390.d029966 m n ≤ 1 := by
  have hmin := _root_.GD.N0101.N0393.d029959
    (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029964) (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029965)
  calc
    _ ≤ ∫ z, _root_.GD.N0232.N0720.N1436.d013273 m n _root_.GD.N0101.N0390.d029964.1 z ∂_root_.GD.N0232.N0720.N1436.d013288 :=
      integral_mono hmin (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029964) (fun _ => min_le_left _ _)
    _ = 1 := _root_.GD.N0101.N0390.d029967 m n hm hn _root_.GD.N0101.N0390.d029964


theorem d029971 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    _root_.GD.N0101.N0390.d029966 m n / 8 ≤
      (∫ z, (g z - _root_.GD.N0101.N0390.d029964.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n _root_.GD.N0101.N0390.d029964) +
      (∫ z, (g z - _root_.GD.N0101.N0390.d029965.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n _root_.GD.N0101.N0390.d029965) := by
  rw [_root_.GD.N0045.d021923 m n hm hn _root_.GD.N0101.N0390.d029964,
    _root_.GD.N0045.d021923 m n hm hn _root_.GD.N0101.N0390.d029965]
  have h := _root_.GD.N0101.N0393.d029960 (g := g) (a := _root_.GD.N0101.N0390.d029964.1) (b := _root_.GD.N0101.N0390.d029965.1)
    ((_root_.GD.N0045.d021922 m n hm hn _root_.GD.N0101.N0390.d029964).mono (fun _ h => h.le))
    ((_root_.GD.N0045.d021922 m n hm hn _root_.GD.N0101.N0390.d029965).mono (fun _ h => h.le))
    (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029964) (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029965)
    (_root_.GD.N0045.d021928 m n hm hn _root_.GD.N0101.N0390.d029964 g hg hB _root_.GD.N0101.N0390.d029964.1)
    (_root_.GD.N0045.d021928 m n hm hn _root_.GD.N0101.N0390.d029965 g hg hB _root_.GD.N0101.N0390.d029965.1)
  norm_num only [_root_.GD.N0101.N0390.d029964, _root_.GD.N0101.N0390.d029965] at h ⊢
  dsimp only [_root_.GD.N0101.N0390.d029966, _root_.GD.N0101.N0390.d029964, _root_.GD.N0101.N0390.d029965]
  linarith


theorem d029972 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {C : ℝ} (hC : 0 ≤ C) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ)) :
    1 + _root_.GD.N0101.N0390.d029966 m n / 3 ≤ C := by
  obtain ⟨g, hg, hb, hred⟩ := _root_.GD.N0045.d023068 m n hm hn C hC d hd hcap
  have hB : ∀ z, |g z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (hb z).1]
    exact (hb z).2
  have h := _root_.GD.N0101.N0390.d029971 m n hm hn g hg hB
  have hl := hred _root_.GD.N0101.N0390.d029964
  have hr := hred _root_.GD.N0101.N0390.d029965
  norm_num only [_root_.GD.N0101.N0390.d029964, _root_.GD.N0101.N0390.d029965] at h hl hr
  linarith



theorem d029973
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ENNReal.ofReal (1 + _root_.GD.N0101.N0390.d029966 m n / 3) ≤ _root_.GD.N0232.N0720.N1256.d015549 m n := by
  by_cases htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨d, hd, hv⟩ := _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
  let C := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015549 m n := ENNReal.ofReal_toReal htop
  have hcap (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
    apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC θ d).mp
    rw [hval, ← hv]
    exact le_iSup (fun η => _root_.GD.N0232.N0720.N1256.d015547 m n η d) θ
  rw [← hval]
  exact ENNReal.ofReal_le_ofReal (_root_.GD.N0101.N0390.d029972 m n hm hn hC d hd.1.1 hcap)



theorem d029974 {k : ℕ}
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (i j : Fin k) (hij : i ≠ j) :
    ENNReal.ofReal (1 + _root_.GD.N0101.N0390.d029966 (sizes i) (sizes j) / 3) ≤
      _root_.GD.N0232.N0719.N0962.d012188 k sizes :=
  (_root_.GD.N0101.N0390.d029973 (sizes i) (sizes j) (hn i) (hn j)).trans
    (_root_.GD.N0036.d022918 sizes hn i j hij)

end
end GD.N0101.N0390

#print axioms _root_.GD.N0101.N0390.d029969
#print axioms _root_.GD.N0101.N0390.d029970
#print axioms _root_.GD.N0101.N0390.d029971
#print axioms _root_.GD.N0101.N0390.d029972
#print axioms _root_.GD.N0101.N0390.d029973
#print axioms _root_.GD.N0101.N0390.d029974
