


























import GD.Module0077

namespace GD
namespace N0230
namespace N0690

open scoped ENNReal RealInnerProductSpace
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0694



section Abstract

variable {E : Type*} [MetricSpace E]



theorem d001034 (U V : E → E) {L : ℝ}
    (hVU : ∀ x, V (U x) = x) (hV : ∀ x y, dist (V x) (V y) ≤ L * dist x y)
    {d : E} (hd : U d = d) (e : E) :
    dist e d ≤ L * dist (U e) d := by
  have h := hV (U e) (U d)
  rw [hVU e, hVU d] at h
  rw [hd] at h
  exact h



theorem d001035 {d e : E}
    (h : ∀ ε > 0, ∃ (U V : E → E) (L : ℝ), (∀ x, V (U x) = x) ∧
      (∀ x y, dist (V x) (V y) ≤ L * dist x y) ∧ U d = d ∧
      L * dist (U e) d < ε) :
    e = d := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨U, V, L, hVU, hV, hd, hlt⟩ := h ε hε
  exact (_root_.GD.N0230.N0690.d001034 U V hVU hV hd e).trans hlt.le



theorem d001036 {Θ : Type*}
    (risk : Θ → E → ℝ≥0∞) (d : E)
    (h : ∀ e, _root_.GD.N0230.N0608.d000672 risk e d → ∀ ε > 0,
      ∃ (U V : E → E) (L : ℝ), (∀ x, V (U x) = x) ∧
        (∀ x y, dist (V x) (V y) ≤ L * dist x y) ∧ U d = d ∧
        L * dist (U e) d < ε) :
    _root_.GD.N0230.N0608.d000674 risk d :=
  fun e he => _root_.GD.N0230.N0690.d001035 (h e he)

end Abstract



theorem d001037 (j : ℤ) : _root_.GD.N0230.N0694.d000983 j = ((2 : ℝ) ^ j.natAbs)⁻¹ := by
  rw [_root_.GD.N0230.N0694.d000983, zpow_neg, zpow_natCast]

theorem d001038 (k : ℤ) : _root_.GD.N0230.N0694.d000983 0 / _root_.GD.N0230.N0694.d000983 k = (2 : ℝ) ^ k.natAbs := by
  rw [_root_.GD.N0230.N0694.d000986, _root_.GD.N0230.N0690.d001037, one_div, inv_inv]

theorem d001039 (k : ℤ) : _root_.GD.N0230.N0694.d001000 k (0 : lp (fun _ : ℤ => ℝ) 2) = 0 := by
  apply lp.ext
  funext j
  simp [_root_.GD.N0230.N0694.d001001, lp.coeFn_zero]

theorem d001040 (k : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) :
    _root_.GD.N0230.N0694.d001000 (-k) (_root_.GD.N0230.N0694.d001000 k x) = x := by
  rw [_root_.GD.N0230.N0694.d001003, neg_add_cancel, _root_.GD.N0230.N0694.d001002]


theorem d001041 (k : ℤ) {L : ℝ}
    (hL : ∀ x y, dist (_root_.GD.N0230.N0694.d001000 (-k) x) (_root_.GD.N0230.N0694.d001000 (-k) y) ≤ L * dist x y) :
    (2 : ℝ) ^ k.natAbs ≤ L := by
  have h := hL (lp.single (E := fun _ : ℤ => ℝ) 2 k 1) 0
  rw [_root_.GD.N0230.N0690.d001039, _root_.GD.N0230.N0694.d001010, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero,
    _root_.GD.N0230.N0694.d001012, _root_.GD.N0230.N0694.d001012, add_neg_cancel, mul_one, _root_.GD.N0230.N0690.d001038,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k.natAbs), abs_one, mul_one] at h
  exact h


theorem d001042 (a : ℝ) (k : ℤ) :
    dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992 = |a| * _root_.GD.N0230.N0694.d000983 k := by
  rw [_root_.GD.N0230.N0694.d001004, _root_.GD.N0230.N0694.d001006, _root_.GD.N0230.N0694.d001005, _root_.GD.N0230.N0694.d001011, dist_eq_norm]
  have h : _root_.GD.N0230.N0694.d000992 + a • lp.single (E := fun _ : ℤ => ℝ) 2 k (_root_.GD.N0230.N0694.d000983 k) - _root_.GD.N0230.N0694.d000992 =
      a • lp.single (E := fun _ : ℤ => ℝ) 2 k (_root_.GD.N0230.N0694.d000983 k) := by abel
  rw [h, norm_smul, _root_.GD.N0230.N0694.d001012, Real.norm_eq_abs, abs_of_pos (_root_.GD.N0230.N0694.d000984 k)]



theorem d001043 (a : ℝ) (k : ℤ) :
    (2 : ℝ) ^ k.natAbs * dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992 = |a| := by
  rw [_root_.GD.N0230.N0690.d001042, _root_.GD.N0230.N0690.d001037]
  have h : (2 : ℝ) ^ k.natAbs ≠ 0 := by positivity
  field_simp




theorem d001044 (a : ℝ) (k : ℤ) {L : ℝ}
    (hL : ∀ x y, dist (_root_.GD.N0230.N0694.d001000 (-k) x) (_root_.GD.N0230.N0694.d001000 (-k) y) ≤ L * dist x y) :
    |a| ≤ L * dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992 := by
  have h1 := _root_.GD.N0230.N0690.d001041 k hL
  have h2 := _root_.GD.N0230.N0690.d001043 a k
  have h3 : 0 ≤ dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992 := dist_nonneg
  calc |a| = (2 : ℝ) ^ k.natAbs * dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992 := h2.symm
    _ ≤ L * dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992 :=
        mul_le_mul_of_nonneg_right h1 h3


theorem d001045 (a : ℝ) (k : ℤ) :
    _root_.GD.N0230.N0694.d001014 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008) =
      ENNReal.ofReal (‖_root_.GD.N0230.N0694.d000992‖ ^ 2 - (2 * a - a ^ 2) * _root_.GD.N0230.N0694.d000983 (-k) ^ 2) := by
  rw [_root_.GD.N0230.N0694.d001014, _root_.GD.N0230.N0694.d001004, _root_.GD.N0230.N0694.d001006, _root_.GD.N0230.N0694.d001005, _root_.GD.N0230.N0694.d001011]
  congr 1
  have hre : _root_.GD.N0230.N0694.d000992 + a • lp.single (E := fun _ : ℤ => ℝ) 2 (-k) (_root_.GD.N0230.N0694.d000983 (-k)) - (2 : ℝ) • _root_.GD.N0230.N0694.d000992 =
      a • lp.single (E := fun _ : ℤ => ℝ) 2 (-k) (_root_.GD.N0230.N0694.d000983 (-k)) - _root_.GD.N0230.N0694.d000992 := by
    rw [two_smul]; abel
  rw [hre, norm_sub_sq_real, real_inner_smul_left, _root_.GD.N0230.N0694.d001013, norm_smul,
    _root_.GD.N0230.N0694.d001012, Real.norm_eq_abs, mul_pow, sq_abs, abs_of_pos (_root_.GD.N0230.N0694.d000984 (-k))]
  ring



theorem d001046 {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    _root_.GD.N0230.N0608.d000675 _root_.GD.N0230.N0694.d001014 (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008) _root_.GD.N0230.N0694.d000992 := by
  intro k
  rw [_root_.GD.N0230.N0690.d001045, _root_.GD.N0230.N0694.d001019]
  apply (ENNReal.ofReal_lt_ofReal_iff (pow_pos _root_.GD.N0230.N0694.d000995 2)).mpr
  have hw := pow_pos (_root_.GD.N0230.N0694.d000984 (-k)) 2
  have hpos : 0 < (2 * a - a ^ 2) * _root_.GD.N0230.N0694.d000983 (-k) ^ 2 := mul_pos (by nlinarith) hw
  linarith

theorem d001047 {a : ℝ} (ha : a ≠ 0) : _root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008 ≠ _root_.GD.N0230.N0694.d000992 := by
  intro h
  have h0 : a • _root_.GD.N0230.N0694.d001008 = 0 := by simpa using congrArg (fun z => z - _root_.GD.N0230.N0694.d000992) h
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact ha h1
  · exact _root_.GD.N0230.N0694.d001009 h1





theorem d001048 {c : ℝ} (hc : 0 < c) (hc2 : c < 2) :
    ∃ e : lp (fun _ : ℤ => ℝ) 2,
      _root_.GD.N0230.N0608.d000675 _root_.GD.N0230.N0694.d001014 e _root_.GD.N0230.N0694.d000992 ∧ e ≠ _root_.GD.N0230.N0694.d000992 ∧
      ∀ (k : ℤ) (L : ℝ),
        (∀ x y, dist (_root_.GD.N0230.N0694.d001000 (-k) x) (_root_.GD.N0230.N0694.d001000 (-k) y) ≤ L * dist x y) →
          c ≤ L * dist (_root_.GD.N0230.N0694.d001000 k e) _root_.GD.N0230.N0694.d000992 := by
  refine ⟨_root_.GD.N0230.N0694.d000992 + c • _root_.GD.N0230.N0694.d001008, _root_.GD.N0230.N0690.d001046 hc hc2,
    _root_.GD.N0230.N0690.d001047 hc.ne', fun k L hL => ?_⟩
  have h := _root_.GD.N0230.N0690.d001044 c k hL
  rwa [abs_of_pos hc] at h



#print axioms _root_.GD.N0230.N0690.d001034
#print axioms _root_.GD.N0230.N0690.d001035
#print axioms _root_.GD.N0230.N0690.d001036
#print axioms _root_.GD.N0230.N0690.d001041
#print axioms _root_.GD.N0230.N0690.d001043
#print axioms _root_.GD.N0230.N0690.d001044
#print axioms _root_.GD.N0230.N0690.d001046
#print axioms _root_.GD.N0230.N0690.d001048

end N0690
end N0230
end GD
