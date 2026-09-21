import GD.Module1163
import GD.Module1183
import GD.Module1179

























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1048

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1506
open _root_.GD.N0232.N0720.N1470
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1047

variable (m n : ℕ)





theorem d019044
    (s d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s d)
    (hnorm : ‖d‖ ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖) :
    d = _root_.GD.N0232.N0720.N1159.d014633 m n s := by
  set u := _root_.GD.N0232.N0720.N1159.d014633 m n s with hu
  have hu_mem : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s u := (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  have hconv := _root_.GD.N0232.N0720.N1159.d014632 m n s
  have hmid_mem : (2 : ℝ)⁻¹ • (u + d) ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s := by
    have h := hconv (show u ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s from hu_mem)
      (show d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s from hd)
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
    simpa [smul_add] using h
  have hmin := (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.2 _ hmid_mem
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hmin
  simp only [zero_sub, norm_neg] at hmin
  have hmin' : ‖u‖ ^ 2 ≤ ‖(2 : ℝ)⁻¹ • (u + d)‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hmin
  have hmidnorm : ‖(2 : ℝ)⁻¹ • (u + d)‖ = 2⁻¹ * ‖u + d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [hmidnorm] at hmin'
  have hpar := parallelogram_law_with_norm ℝ u d
  have hnormsq : ‖d‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [hnorm, norm_nonneg d, norm_nonneg u]
  have hdiff : ‖u - d‖ * ‖u - d‖ ≤ 0 := by
    nlinarith [hpar, hmin', hnormsq, norm_nonneg (u + d)]
  have hzero : ‖u - d‖ = 0 := by nlinarith [norm_nonneg (u - d)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm



theorem d019045
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (T : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hmaps : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s (T (_root_.GD.N0232.N0720.N1159.d014633 m n s)))
    (hnorm : ‖T (_root_.GD.N0232.N0720.N1159.d014633 m n s)‖ ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖) :
    T (_root_.GD.N0232.N0720.N1159.d014633 m n s) = _root_.GD.N0232.N0720.N1159.d014633 m n s :=
  _root_.GD.N0232.N0720.N1048.d019044 m n s _ hmaps hnorm





theorem d019046 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1446.d019032 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  apply _root_.GD.N0232.N0720.N1048.d019045
  · intro θ
    rw [_root_.GD.N0232.N0720.N1446.d019037]
    calc _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        ≤ _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) s.value :=
          (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1 _
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n θ s.value := _root_.GD.N0232.N0720.N1446.d019039 m n s θ
  · exact (_root_.GD.N0232.N0720.N1446.d019036 m n _).le



theorem d019047 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
      _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  rw [← _root_.GD.N0232.N0720.N1446.d019037, _root_.GD.N0232.N0720.N1048.d019046]



theorem d019048 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    _root_.GD.N0232.N0720.N1506.d019007 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value :=
  _root_.GD.N0232.N0720.N1506.d019015 m n _
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1 g



variable (hm : 2 ≤ m) (hn : 2 ≤ n)


theorem d019049 :
    _root_.GD.N0232.N0720.N1446.d019032 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) =
      _root_.GD.N0232.N0720.N1047.d018650 m n hm hn :=
  _root_.GD.N0232.N0720.N1048.d019046 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn)


theorem d019050 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) =
      _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) :=
  _root_.GD.N0232.N0720.N1048.d019047 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) θ


theorem d019051 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    _root_.GD.N0232.N0720.N1506.d019007 m n g (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) =
      _root_.GD.N0232.N0720.N1047.d018650 m n hm hn :=
  _root_.GD.N0232.N0720.N1048.d019048 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) g


theorem d019052 :
    _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) =
      _root_.GD.N0232.N0720.N1047.d018650 m n hm hn :=
  _root_.GD.N0232.N0720.N1470.d018969 m n hm hn _
    (_root_.GD.N0232.N0720.N1047.d018652 m n hm hn)



theorem d019053 :
    ∃ g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable g ∧
        (fun ω ↦ (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) ω) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n :=
  _root_.GD.N0232.N0720.N1470.d018970 m n hm hn _
    (_root_.GD.N0232.N0720.N1047.d018652 m n hm hn)

end

end N1048
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1048.d019044
#print axioms _root_.GD.N0232.N0720.N1048.d019046
#print axioms _root_.GD.N0232.N0720.N1048.d019047
#print axioms _root_.GD.N0232.N0720.N1048.d019048
#print axioms _root_.GD.N0232.N0720.N1048.d019049
#print axioms _root_.GD.N0232.N0720.N1048.d019051
#print axioms _root_.GD.N0232.N0720.N1048.d019052
#print axioms _root_.GD.N0232.N0720.N1048.d019053
