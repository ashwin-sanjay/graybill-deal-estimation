import GD.Module1183
















open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1087

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0624
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1506
open _root_.GD.N0232.N0720.N1446

variable (m n : ℕ)


theorem d019088 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1446.d019019 m n (_root_.GD.N0232.N0720.N1506.d018998 m n g ω) =
      _root_.GD.N0232.N0720.N1506.d018998 m n g (_root_.GD.N0232.N0720.N1446.d019019 m n ω) :=
  Prod.ext rfl rfl


theorem d019089 (g : _root_.GD.N0232.N0720.N1506.d018997 m n)
    (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1446.d019032 m n (_root_.GD.N0232.N0720.N1506.d019007 m n g x) =
      _root_.GD.N0232.N0720.N1506.d019007 m n g (_root_.GD.N0232.N0720.N1446.d019032 m n x) := by
  unfold _root_.GD.N0232.N0720.N1446.d019032 _root_.GD.N0232.N0720.N1506.d019007
  rw [map_neg]
  congr 1
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  exact _root_.GD.N0232.N0720.N1506.d019008
    (by funext ω; exact _root_.GD.N0232.N0720.N1087.d019088 m n g ω) _ _ x



theorem d019090 (g : _root_.GD.N0232.N0720.N1506.d018997 m n)
    (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (he : _root_.GD.N0232.N0720.N1506.d019007 m n g e = e) :
    _root_.GD.N0232.N0720.N1506.d019007 m n g ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) =
      (2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e) := by
  have hsmul := LinearMap.map_smul (Lp.compMeasurePreservingₗ ℝ (_root_.GD.N0232.N0720.N1506.d018998 m n g)
    (_root_.GD.N0232.N0720.N1506.d019006 m n g)) ((2 : ℝ)⁻¹)
    (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)
  have hadd := map_add (Lp.compMeasurePreserving (_root_.GD.N0232.N0720.N1506.d018998 m n g)
    (_root_.GD.N0232.N0720.N1506.d019006 m n g)) e (_root_.GD.N0232.N0720.N1446.d019032 m n e)
  change _root_.GD.N0232.N0720.N1506.d019007 m n g ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) =
    (2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)
  have h1 : _root_.GD.N0232.N0720.N1506.d019007 m n g ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) =
      (2 : ℝ)⁻¹ • _root_.GD.N0232.N0720.N1506.d019007 m n g (e + _root_.GD.N0232.N0720.N1446.d019032 m n e) := hsmul
  have h2 : _root_.GD.N0232.N0720.N1506.d019007 m n g (e + _root_.GD.N0232.N0720.N1446.d019032 m n e) =
      _root_.GD.N0232.N0720.N1506.d019007 m n g e + _root_.GD.N0232.N0720.N1506.d019007 m n g (_root_.GD.N0232.N0720.N1446.d019032 m n e) := hadd
  rw [h1, h2, ← _root_.GD.N0232.N0720.N1087.d019089, he]


theorem d019091
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdperm : ∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g d = d)
    (hdrefl : _root_.GD.N0232.N0720.N1446.d019032 m n d = d)
    (hsym : ∀ e, (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g e = e) → _root_.GD.N0232.N0720.N1446.d019032 m n e = e →
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d → e = d)
    (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (heperm : ∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g e = e)
    (he : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d) : e = d := by

  set r := _root_.GD.N0232.N0720.N1446.d019032 m n e with hr
  set mid : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := (2 : ℝ)⁻¹ • (e + r) with hmid
  have hprof : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) d = _root_.GD.N0232.N0720.N1080.d014182 m n θ d := by
    intro θ
    rw [← _root_.GD.N0232.N0720.N1446.d019037, hdrefl]
  have hmidfix : _root_.GD.N0232.N0720.N1446.d019032 m n mid = mid := by
    rw [hmid, _root_.GD.N0232.N0720.N1446.d019035, _root_.GD.N0232.N0720.N1446.d019034, ← hr,
      _root_.GD.N0232.N0720.N1446.d019033, add_comm]
  have hmidperm : ∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g mid = mid := fun g =>
    _root_.GD.N0232.N0720.N1087.d019090 m n g e (heperm g)
  have hmiddom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) mid d := by
    intro θ
    have h := _root_.GD.N0232.N0720.N1506.d019013 m n (G := Fin 2) θ ![e, r]
    simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Nat.cast_ofNat] at h
    have hr_risk : _root_.GD.N0232.N0720.N1080.d014182 m n θ r ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ d := by
      rw [hr, _root_.GD.N0232.N0720.N1446.d019037]
      exact (he _).trans (le_of_eq (hprof θ))
    calc _root_.GD.N0232.N0720.N1080.d014182 m n θ mid ≤ (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ e + _root_.GD.N0232.N0720.N1080.d014182 m n θ r) := h
      _ ≤ (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ d + _root_.GD.N0232.N0720.N1080.d014182 m n θ d) :=
          mul_le_mul_right (add_le_add (he θ) hr_risk) _
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n θ d := by
          rw [← two_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hmideq : mid = d := hsym mid hmidperm hmidfix hmiddom
  have hnorm_le : ‖e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    have h := he _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at h
    simp only [zero_sub, norm_neg] at h
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h
  have hnr : ‖r‖ = ‖e‖ := by rw [hr, _root_.GD.N0232.N0720.N1446.d019036]
  have hsum : ‖e + r‖ = 2 * ‖d‖ := by
    have : ‖mid‖ = (2 : ℝ)⁻¹ * ‖e + r‖ := by
      rw [hmid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    rw [hmideq] at this
    linarith
  have hpar := parallelogram_law_with_norm ℝ e r
  rw [hnr, hsum] at hpar
  have hzero : ‖e - r‖ = 0 := by
    have hdiff : ‖e - r‖ * ‖e - r‖ ≤ 0 := by nlinarith [hpar, hnorm_le]
    nlinarith [norm_nonneg (e - r)]
  have her : e = r := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hmid_e : mid = e := by
    rw [hmid, ← her, ← two_smul ℝ e, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [← hmid_e, hmideq]




theorem d019092
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdperm : ∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g d = d)
    (hdrefl : _root_.GD.N0232.N0720.N1446.d019032 m n d = d)
    (hsym : ∀ e, (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g e = e) → _root_.GD.N0232.N0720.N1446.d019032 m n e = e →
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d → e = d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d :=
  _root_.GD.N0230.N0624.d000783 (_root_.GD.N0232.N0720.N1506.d019014 m n) d hdperm
    (fun e heperm he => _root_.GD.N0232.N0720.N1087.d019091 m n d hdperm hdrefl hsym e heperm he)


theorem d019093
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g s.value = s.value) ∧
          _root_.GD.N0232.N0720.N1446.d019032 m n s.value = s.value ∧
          ∀ e, (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g e = e) → _root_.GD.N0232.N0720.N1446.d019032 m n e = e →
            _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e s.value → e = s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, hs,
      fun g => _root_.GD.N0232.N0720.N1506.d019015 m n s.value ht g,
      _root_.GD.N0232.N0720.N1446.d019040 m n s ht,
      fun e _ _ he => ht e he⟩
  · rintro ⟨s, hs, hperm, hrefl, hsym⟩
    exact ⟨s, hs, _root_.GD.N0232.N0720.N1087.d019092 m n s.value hperm hrefl hsym⟩

end

end N1087
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1087.d019089
#print axioms _root_.GD.N0232.N0720.N1087.d019092
#print axioms _root_.GD.N0232.N0720.N1087.d019093
