import GD.Module1187
import GD.Module1179






















open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1216

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1087
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1470
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1506

variable (m n : ℕ)



theorem d019231
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (he : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d)
    (hprojection : _root_.GD.N0232.N0720.N1501.d016291 m n e = d) :
    e = d := by
  have hfinite : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n]
    exact ENNReal.ofReal_ne_top
  have hle : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) := by
    rw [hprojection]
    exact he _root_.GD.N0232.N0720.N1080.d014169
  have hprojectedFinite :
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hfinite
      (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 e)
  have heq : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e =
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) :=
    le_antisymm hle (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 e)
  have hreal : (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e).toReal =
      (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e)).toReal := by
    rw [heq]
  rw [_root_.GD.N0232.N0720.N1128.d017097 m n _root_.GD.N0232.N0720.N1080.d014169 e hfinite,
    _root_.GD.N0232.N0720.N1128.d017097 m n _root_.GD.N0232.N0720.N1080.d014169
      (_root_.GD.N0232.N0720.N1501.d016291 m n e) hprojectedFinite] at hreal
  have hintegrable :=
    _root_.GD.N0232.N0720.N1078.d016376 m n _root_.GD.N0232.N0720.N1080.d014169 e hfinite
  have hfixed : e = _root_.GD.N0232.N0720.N1501.d016291 m n e :=
    (_root_.GD.N0232.N0720.N1501.d016305
      m n hm hn _root_.GD.N0232.N0720.N1080.d014169 e hintegrable).1 hreal
  exact hfixed.trans hprojection



theorem d019232 (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1501.d016291 m n e) = _root_.GD.N0232.N0720.N1501.d016291 m n e :=
  _root_.GD.N0232.N0720.N1470.d018968 m n e



def d019233
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ e, (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g e = e) →
    _root_.GD.N0232.N0720.N1446.d019032 m n e = e →
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1501.d016291 m n e) d →
    _root_.GD.N0232.N0720.N1501.d016291 m n e = d





theorem d019234
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hprofile : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) d = _root_.GD.N0232.N0720.N1080.d014182 m n theta d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d ↔
      (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g d = d) ∧
      _root_.GD.N0232.N0720.N1446.d019032 m n d = d ∧
      _root_.GD.N0232.N0720.N1216.d019233 m n d := by
  constructor
  · intro hd
    exact ⟨
      fun g => _root_.GD.N0232.N0720.N1506.d019015 m n d hd g,
      _root_.GD.N0232.N0720.N1446.d019038 m n d hprofile hd,
      fun e _ _ he => hd _ he⟩
  · rintro ⟨hdperm, hdrefl, hprojected⟩
    apply _root_.GD.N0232.N0720.N1087.d019092
      m n d hdperm hdrefl
    intro e heperm herefl he
    have hpdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1501.d016291 m n e) d :=
      fun theta => (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta e).trans (he theta)
    have hpeq : _root_.GD.N0232.N0720.N1501.d016291 m n e = d :=
      hprojected e heperm herefl hpdom
    exact _root_.GD.N0232.N0720.N1216.d019231
      m n hm hn he hpeq



def d019235
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ e, _root_.GD.N0232.N0720.N1446.d019032 m n e = e →
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1501.d016291 m n e) d →
    _root_.GD.N0232.N0720.N1501.d016291 m n e = d





theorem d019236
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hprofile : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) d = _root_.GD.N0232.N0720.N1080.d014182 m n theta d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d ↔
      _root_.GD.N0232.N0720.N1216.d019235 m n d := by
  constructor
  · intro hd e _ he
    exact hd _ he
  · intro hprojected e he
    set r := _root_.GD.N0232.N0720.N1446.d019032 m n e with hr
    set mid : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := (2 : ℝ)⁻¹ • (e + r) with hmid
    have hmidfix : _root_.GD.N0232.N0720.N1446.d019032 m n mid = mid := by
      rw [hmid, _root_.GD.N0232.N0720.N1446.d019035, _root_.GD.N0232.N0720.N1446.d019034, ← hr,
        _root_.GD.N0232.N0720.N1446.d019033, add_comm]
    have hmiddom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) mid d := by
      intro theta
      have havg := _root_.GD.N0232.N0720.N1506.d019013 m n (G := Fin 2) theta ![e, r]
      simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Nat.cast_ofNat] at havg
      have hrisk : _root_.GD.N0232.N0720.N1080.d014182 m n theta r ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta d := by
        rw [hr, _root_.GD.N0232.N0720.N1446.d019037]
        exact (he _).trans (le_of_eq (hprofile theta))
      calc
        _root_.GD.N0232.N0720.N1080.d014182 m n theta mid ≤
            (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 m n theta e + _root_.GD.N0232.N0720.N1080.d014182 m n theta r) := havg
        _ ≤ (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 m n theta d + _root_.GD.N0232.N0720.N1080.d014182 m n theta d) :=
          mul_le_mul_right (add_le_add (he theta) hrisk) _
        _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta d := by
          rw [← two_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    have hpdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1501.d016291 m n mid) d :=
      fun theta =>
        (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta mid).trans (hmiddom theta)
    have hpeq : _root_.GD.N0232.N0720.N1501.d016291 m n mid = d :=
      hprojected mid hmidfix hpdom
    have hmideq : mid = d :=
      _root_.GD.N0232.N0720.N1216.d019231
        m n hm hn hmiddom hpeq
    have hnorm_le : ‖e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
      have href := he _root_.GD.N0232.N0720.N1080.d014169
      rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
      simp only [zero_sub, norm_neg] at href
      exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp href
    have hnr : ‖r‖ = ‖e‖ := by
      rw [hr, _root_.GD.N0232.N0720.N1446.d019036]
    have hsum : ‖e + r‖ = 2 * ‖d‖ := by
      have hnormMid : ‖mid‖ = (2 : ℝ)⁻¹ * ‖e + r‖ := by
        rw [hmid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [hmideq] at hnormMid
      linarith
    have hpar := parallelogram_law_with_norm ℝ e r
    rw [hnr, hsum] at hpar
    have hdiff : ‖e - r‖ * ‖e - r‖ ≤ 0 := by
      nlinarith [hpar, hnorm_le]
    have hzero : ‖e - r‖ = 0 := by
      nlinarith [norm_nonneg (e - r)]
    have her : e = r := sub_eq_zero.mp (norm_eq_zero.mp hzero)
    have hmid_e : mid = e := by
      rw [hmid, ← her, ← two_smul ℝ e, smul_smul,
        inv_mul_cancel₀ (by norm_num), one_smul]
    rw [← hmid_e, hmideq]



theorem d019237
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hprofile : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) d = _root_.GD.N0232.N0720.N1080.d014182 m n theta d)
    (hprojected : _root_.GD.N0232.N0720.N1216.d019235 m n d) :
    _root_.GD.N0232.N0720.N1501.d016291 m n d = d ∧
      _root_.GD.N0232.N0720.N1446.d019032 m n d = d ∧
      ∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g d = d := by
  have hstrong :=
    (_root_.GD.N0232.N0720.N1216.d019236
      m n hm hn d hprofile).2 hprojected
  exact ⟨_root_.GD.N0232.N0720.N1470.d018969 m n hm hn d hstrong,
    _root_.GD.N0232.N0720.N1446.d019038 m n d hprofile hstrong,
    fun g => _root_.GD.N0232.N0720.N1506.d019015 m n d hstrong g⟩




theorem d019238
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1216.d019235 m n s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, hstrong⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1216.d019236
        m n hm hn s.value (_root_.GD.N0232.N0720.N1446.d019039 m n s)).1 hstrong⟩
  · rintro ⟨s, hs, hprojected⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1216.d019236
        m n hm hn s.value (_root_.GD.N0232.N0720.N1446.d019039 m n s)).2 hprojected⟩

end

end N1216
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1216.d019231
#print axioms _root_.GD.N0232.N0720.N1216.d019236
#print axioms _root_.GD.N0232.N0720.N1216.d019237
#print axioms _root_.GD.N0232.N0720.N1216.d019238
