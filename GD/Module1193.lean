import GD.Module1183











open MeasureTheory Filter
open scoped BigOperators

namespace GD.N0232.N0720.N1295

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1506 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0137 _root_.GD.N0107

variable (m n : ℕ)


def d019239 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ∀ b a omega, 0 < a →
    d (_root_.GD.N0107.d009024 m n b a a omega) = b + a * d omega

theorem d019240 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1295.d019239 m n d ↔
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) d := by
  constructor
  · intro hd g omega
    exact hd g.shift g.d009239 omega g.d009240
  · intro hd b a omega ha
    have h := hd (⟨b, Real.log a⟩ : _root_.GD.N0232.N0719.N0946.d009229) omega
    simpa only [_root_.GD.N0232.N0720.N1214.d014259, _root_.GD.N0232.N0719.N0946.d009229.d009244,
      _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_log ha] using h


def d019241 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  (Fintype.card (_root_.GD.N0232.N0720.N1506.d018997 m n) : ℝ)⁻¹ *
    ∑ g : _root_.GD.N0232.N0720.N1506.d018997 m n, d (_root_.GD.N0232.N0720.N1506.d018998 m n g omega)


def d019242 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  (_root_.GD.N0232.N0720.N1295.d019241 m n d omega -
    _root_.GD.N0232.N0720.N1295.d019241 m n d (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) / 2

theorem d019243 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : Measurable d) : Measurable (_root_.GD.N0232.N0720.N1295.d019241 m n d) := by
  classical
  unfold _root_.GD.N0232.N0720.N1295.d019241
  exact measurable_const.mul
    (Finset.measurable_sum _ (fun g _ ↦
      hd.comp (_root_.GD.N0232.N0720.N1506.d019001 m n g)))

theorem d019244 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : Measurable d) : Measurable (_root_.GD.N0232.N0720.N1295.d019242 m n d) := by
  exact ((_root_.GD.N0232.N0720.N1295.d019243 m n hd).sub
    ((_root_.GD.N0232.N0720.N1295.d019243 m n hd).comp
      (_root_.GD.N0232.N0720.N1446.d019021 m n))).div_const 2

theorem d019245 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (g : _root_.GD.N0232.N0720.N1506.d018997 m n) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1295.d019241 m n d (_root_.GD.N0232.N0720.N1506.d018998 m n g omega) =
      _root_.GD.N0232.N0720.N1295.d019241 m n d omega := by
  classical
  unfold _root_.GD.N0232.N0720.N1295.d019241
  congr 1
  calc
    (∑ h : _root_.GD.N0232.N0720.N1506.d018997 m n, d (_root_.GD.N0232.N0720.N1506.d018998 m n h
        (_root_.GD.N0232.N0720.N1506.d018998 m n g omega))) =
        ∑ h : _root_.GD.N0232.N0720.N1506.d018997 m n, d (_root_.GD.N0232.N0720.N1506.d018998 m n (g * h) omega) := by
      apply Finset.sum_congr rfl
      intro h _
      exact congrArg d (congrFun (_root_.GD.N0232.N0720.N1506.d019000 m n g h) omega)
    _ = ∑ h : _root_.GD.N0232.N0720.N1506.d018997 m n, d (_root_.GD.N0232.N0720.N1506.d018998 m n h omega) :=
      Equiv.sum_comp (Equiv.mulLeft g) (fun h ↦ d (_root_.GD.N0232.N0720.N1506.d018998 m n h omega))

theorem d019246 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1446.d019019 m n (_root_.GD.N0232.N0720.N1506.d018998 m n g omega) =
      _root_.GD.N0232.N0720.N1506.d018998 m n g (_root_.GD.N0232.N0720.N1446.d019019 m n omega) := rfl

theorem d019247 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (g : _root_.GD.N0232.N0720.N1506.d018997 m n) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1295.d019242 m n d (_root_.GD.N0232.N0720.N1506.d018998 m n g omega) =
      _root_.GD.N0232.N0720.N1295.d019242 m n d omega := by
  simp only [_root_.GD.N0232.N0720.N1295.d019242, _root_.GD.N0232.N0720.N1295.d019246,
    _root_.GD.N0232.N0720.N1295.d019245]

theorem d019248 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1295.d019242 m n d (_root_.GD.N0232.N0720.N1446.d019019 m n omega) =
      -_root_.GD.N0232.N0720.N1295.d019242 m n d omega := by
  rw [_root_.GD.N0232.N0720.N1295.d019242, _root_.GD.N0232.N0720.N1446.d019020,
    _root_.GD.N0232.N0720.N1295.d019242]
  ring

theorem d019249 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1295.d019239 m n d) : _root_.GD.N0232.N0720.N1295.d019239 m n (_root_.GD.N0232.N0720.N1295.d019241 m n d) := by
  classical
  intro b a omega ha
  have hc : (Fintype.card (_root_.GD.N0232.N0720.N1506.d018997 m n) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := _root_.GD.N0232.N0720.N1506.d018997 m n))
  unfold _root_.GD.N0232.N0720.N1295.d019241
  simp_rw [← _root_.GD.N0232.N0720.N1506.d019004, hd b a _ ha]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hc]

theorem d019250 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1295.d019239 m n d) : _root_.GD.N0232.N0720.N1295.d019239 m n (_root_.GD.N0232.N0720.N1295.d019242 m n d) := by
  intro b a omega ha
  have hp := _root_.GD.N0232.N0720.N1295.d019249 m n hd
  have hneg : _root_.GD.N0232.N0720.N1446.d019019 m n (_root_.GD.N0107.d009024 m n b a a omega) =
      _root_.GD.N0107.d009024 m n (-b) a a (_root_.GD.N0232.N0720.N1446.d019019 m n omega) := by
    simpa only [neg_neg] using
      (_root_.GD.N0232.N0720.N1446.d019029 m n (-b) a a omega).symm
  simp only [_root_.GD.N0232.N0720.N1295.d019242, hneg, hp b a omega ha,
    hp (-b) a (_root_.GD.N0232.N0720.N1446.d019019 m n omega) ha]
  ring



theorem d019251 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    ∃ hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (hmem.toLp d) ∧
        _root_.GD.N0232.N0720.N1159.d014638 m n (hmem.toLp d) := by
  obtain ⟨hmeas, hcov, hstrict, hterminal⟩ := hd
  have hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hmeas
      (ne_top_of_lt (hstrict _root_.GD.N0232.N0720.N1080.d014169))
  let p := hmem.toLp d
  have hrisk (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014197 m n theta d :=
    (_root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem).symm
  have hclass : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p :=
    hmem.coeFn_toLp.symm.trans (_root_.GD.N0232.N0720.N1214.d014267 m n p).symm
  have hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p :=
    ⟨d, hmeas, fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq hclass, hcov⟩
  refine ⟨hmem, ?_,
    _root_.GD.N0232.N0720.N1159.d014653 m n p hrep⟩
  intro e he
  have hraw : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n e) ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    intro theta
    rw [_root_.GD.N0232.N0720.N1215.d014286, ← hrisk theta]
    exact he theta
  apply Lp.ext
  exact (_root_.GD.N0232.N0720.N1214.d014267 m n e).symm.trans
    ((hterminal _ (_root_.GD.N0232.N0720.N1214.d014266 m n e) hraw _root_.GD.N0232.N0720.N1080.d014169).trans
      hmem.coeFn_toLp.symm)

theorem d019252 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    (∀ g : _root_.GD.N0232.N0720.N1506.d018997 m n,
      (d ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d) ∧
      (fun omega ↦ -d (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d := by
  obtain ⟨hmem, ht, hc⟩ := _root_.GD.N0232.N0720.N1295.d019251 m n hd
  have hfinite : _root_.GD.N0232.N0720.N1159.d014637 m n (hmem.toLp d) := by
    intro theta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem]
    exact ne_top_of_lt (hd.2.2.1 theta)
  let seed : _root_.GD.N0232.N0720.N1159.d014639 m n := ⟨hmem.toLp d, hfinite, hc⟩
  constructor
  · intro g
    have hfix := _root_.GD.N0232.N0720.N1506.d019015 m n _ ht g
    have hcomp := hmem.comp_measurePreserving (_root_.GD.N0232.N0720.N1506.d019006 m n g)
    change hcomp.toLp (d ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g) = hmem.toLp d at hfix
    exact (hcomp.toLp_eq_toLp_iff hmem).1 hfix
  · have hfix := _root_.GD.N0232.N0720.N1446.d019040 m n seed ht
    have hneg := (hmem.comp_measurePreserving (_root_.GD.N0232.N0720.N1446.d019031 m n)).neg
    change hneg.toLp (fun omega ↦ -d (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) = hmem.toLp d at hfix
    exact (hneg.toLp_eq_toLp_iff hmem).1 hfix

theorem d019253 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1295.d019242 m n d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d := by
  classical
  obtain ⟨hp, hr⟩ := _root_.GD.N0232.N0720.N1295.d019252 m n hd
  have hc : (Fintype.card (_root_.GD.N0232.N0720.N1506.d018997 m n) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := _root_.GD.N0232.N0720.N1506.d018997 m n))
  have havg : _root_.GD.N0232.N0720.N1295.d019241 m n d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d := by
    filter_upwards [ae_all_iff.2 hp] with omega homega
    unfold _root_.GD.N0232.N0720.N1295.d019241
    simp only [Function.comp_apply] at homega
    simp only [homega, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have havgNeg := (_root_.GD.N0232.N0720.N1446.d019031 m n).quasiMeasurePreserving.ae_eq_comp havg
  apply (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
  filter_upwards [havg, havgNeg, hr] with omega h1 h2 h3
  simp only [Function.comp_apply] at h2
  unfold _root_.GD.N0232.N0720.N1295.d019242
  rw [h1, h2]
  linarith



theorem d019254 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    _root_.GD.N0232.N0720.N1159.d014660 m n (_root_.GD.N0232.N0720.N1295.d019242 m n d) := by
  have hae := _root_.GD.N0232.N0720.N1295.d019253 m n hd
  have hrisk (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1295.d019242 m n d) =
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d := _root_.GD.N0232.N0720.N1159.d014662 m n theta (hae theta)
  refine ⟨_root_.GD.N0232.N0720.N1295.d019244 m n hd.1,
    (_root_.GD.N0232.N0720.N1295.d019240 m n _).1
      (_root_.GD.N0232.N0720.N1295.d019250 m n
        ((_root_.GD.N0232.N0720.N1295.d019240 m n d).2 hd.2.1)), ?_, ?_⟩
  · intro theta
    rw [hrisk]
    exact hd.2.2.1 theta
  · intro e he hdom theta
    exact (hd.2.2.2 e he (fun eta ↦ by simpa only [hrisk] using hdom eta) theta).trans
      (hae theta).symm

end
end GD.N0232.N0720.N1295

#print axioms _root_.GD.N0232.N0720.N1295.d019247
#print axioms _root_.GD.N0232.N0720.N1295.d019248
#print axioms _root_.GD.N0232.N0720.N1295.d019250
#print axioms _root_.GD.N0232.N0720.N1295.d019253
#print axioms _root_.GD.N0232.N0720.N1295.d019254
