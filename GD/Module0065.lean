import GD.Module0055





























open scoped ENNReal BigOperators
open RealInnerProductSpace

namespace GD
namespace N0230
namespace N0624

open _root_.GD.N0230.N0608

variable {Θ H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [Fintype G] [Group G]



structure d000770 (risk : Θ → H → ℝ≥0∞) (θ₀ : Θ) where
  act : G → H → H
  pact : G → Θ → Θ
  act_one : ∀ x, act 1 x = x
  act_mul : ∀ g h x, act g (act h x) = act (g * h) x
  map_add : ∀ g x y, act g (x + y) = act g x + act g y
  map_smul : ∀ g (c : ℝ) x, act g (c • x) = c • act g x
  norm_map : ∀ g x, ‖act g x‖ = ‖x‖
  risk_map : ∀ g θ x, risk θ (act g x) = risk (pact g θ) x
  href : ∀ d, risk θ₀ d = ENNReal.ofReal (‖d‖ ^ 2)
  risk_avg : ∀ θ (x : G → H),
    risk θ ((Fintype.card G : ℝ)⁻¹ • ∑ g, x g) ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ * ∑ g, risk θ (x g)

variable {risk : Θ → H → ℝ≥0∞} {θ₀ : Θ}
variable (A : _root_.GD.N0230.N0624.d000770 (G := G) risk θ₀)


def d000771 (x : H) : Prop := ∀ g, A.act g x = x


def d000772 (x : H) : Prop := ∀ g θ, risk (A.pact g θ) x = risk θ x


theorem d000773 {x : H} (hx : _root_.GD.N0230.N0624.d000771 A x) :
    _root_.GD.N0230.N0624.d000772 A x := by
  intro g θ
  rw [← A.risk_map g θ x, hx g]


noncomputable def d000774 (x : H) : H :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g, A.act g x





theorem d000775
    (d : H) (hprof : _root_.GD.N0230.N0624.d000772 A d) (hd : _root_.GD.N0230.N0608.d000674 risk d) :
    _root_.GD.N0230.N0624.d000771 A d := by
  intro g
  refine hd (A.act g d) (fun θ => ?_)
  rw [A.risk_map g θ d, hprof g θ]



theorem d000776 (g : G) : A.act g 0 = 0 := by
  have h := A.map_smul g 0 0
  simpa using h

theorem d000777 (h : G) (x : G → H) :
    A.act h (∑ g, x g) = ∑ g, A.act h (x g) := by
  classical
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using _root_.GD.N0230.N0624.d000776 A h
  · intro a s _ ih
    rw [Finset.sum_insert ‹a ∉ s›, Finset.sum_insert ‹a ∉ s›, A.map_add, ih]


theorem d000778 (x : H) :
    _root_.GD.N0230.N0624.d000771 A (_root_.GD.N0230.N0624.d000774 A x) := by
  intro h
  unfold _root_.GD.N0230.N0624.d000774
  rw [A.map_smul, _root_.GD.N0230.N0624.d000777]
  congr 1
  have hreindex :
      ∑ g, A.act h (A.act g x) = ∑ g, A.act (h * g) x := by
    apply Finset.sum_congr rfl
    intro g _
    exact A.act_mul h g x
  rw [hreindex]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => A.act g x)

theorem d000779 {x : H} :
    ((Fintype.card G : ℝ)⁻¹ • (Fintype.card G : ℝ) • x) = x := by
  haveI : Nonempty G := ⟨1⟩
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := G)).ne'),
    one_smul]


theorem d000780
    {x : H} (hx : _root_.GD.N0230.N0624.d000771 A x) : _root_.GD.N0230.N0624.d000774 A x = x := by
  unfold _root_.GD.N0230.N0624.d000774
  have hsum : ∑ g, A.act g x = (Fintype.card G : ℝ) • x := by
    rw [Finset.sum_congr rfl (fun g _ => hx g), Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [hsum]
  exact _root_.GD.N0230.N0624.d000779



theorem d000781
    (d : H) (hprof : _root_.GD.N0230.N0624.d000772 A d)
    (e : H) (he : _root_.GD.N0230.N0608.d000672 risk e d) :
    _root_.GD.N0230.N0608.d000672 risk (_root_.GD.N0230.N0624.d000774 A e) d := by
  haveI : Nonempty G := ⟨1⟩
  intro θ
  have h := A.risk_avg θ (fun g => A.act g e)
  have hsum : ∑ g : G, risk θ (A.act g e) ≤ (Fintype.card G : ℝ≥0∞) * risk θ d := by
    calc ∑ g : G, risk θ (A.act g e)
        = ∑ g : G, risk (A.pact g θ) e :=
          Finset.sum_congr rfl (fun g _ => A.risk_map g θ e)
      _ ≤ ∑ g : G, risk (A.pact g θ) d := Finset.sum_le_sum (fun g _ => he _)
      _ = ∑ g : G, risk θ d := Finset.sum_congr rfl (fun g _ => hprof g θ)
      _ = (Fintype.card G : ℝ≥0∞) * risk θ d := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc risk θ (_root_.GD.N0230.N0624.d000774 A e)
      ≤ (Fintype.card G : ℝ≥0∞)⁻¹ * ∑ g : G, risk θ (A.act g e) := h
    _ ≤ (Fintype.card G : ℝ≥0∞)⁻¹ * ((Fintype.card G : ℝ≥0∞) * risk θ d) :=
        mul_le_mul_right hsum _
    _ = risk θ d := by
        rw [← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast (Fintype.card_pos (α := G)).ne')
            (ENNReal.natCast_ne_top _), one_mul]



theorem d000782 (x : G → H) :
    ∑ g, ‖x g - (Fintype.card G : ℝ)⁻¹ • ∑ g', x g'‖ ^ 2 =
      ∑ g, ‖x g‖ ^ 2 -
        (Fintype.card G : ℝ) * ‖(Fintype.card G : ℝ)⁻¹ • ∑ g', x g'‖ ^ 2 := by
  haveI : Nonempty G := ⟨1⟩
  set S := ∑ g', x g' with hS
  set c : ℝ := (Fintype.card G : ℝ)⁻¹ with hc
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G)).ne'
  have hcpos : 0 < c := by
    rw [hc]; exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos (α := G))
  have hexpand : ∀ g, ‖x g - c • S‖ ^ 2 =
      ‖x g‖ ^ 2 - 2 * ⟪x g, c • S⟫ + ‖c • S‖ ^ 2 := fun g => norm_sub_sq_real _ _
  rw [Finset.sum_congr rfl (fun g _ => hexpand g), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hinner : ⟪S, c • S⟫ = c * ‖S‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hnorm : ‖c • S‖ ^ 2 = c ^ 2 * ‖S‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, mul_pow]
  rw [hinner, hnorm]
  have hcc : (Fintype.card G : ℝ) * c = 1 := by
    rw [hc, mul_inv_cancel₀ hcard]
  have : (Fintype.card G : ℝ) * (c ^ 2 * ‖S‖ ^ 2) = c * ‖S‖ ^ 2 := by
    calc (Fintype.card G : ℝ) * (c ^ 2 * ‖S‖ ^ 2)
        = ((Fintype.card G : ℝ) * c) * (c * ‖S‖ ^ 2) := by ring
      _ = c * ‖S‖ ^ 2 := by rw [hcc, one_mul]
  linarith






theorem d000783
    (d : H) (hd : _root_.GD.N0230.N0624.d000771 A d)
    (hsym : ∀ e, _root_.GD.N0230.N0624.d000771 A e → _root_.GD.N0230.N0608.d000672 risk e d → e = d) :
    _root_.GD.N0230.N0608.d000674 risk d := by
  haveI : Nonempty G := ⟨1⟩
  intro e he
  have havgDom : _root_.GD.N0230.N0608.d000672 risk (_root_.GD.N0230.N0624.d000774 A e) d :=
    _root_.GD.N0230.N0624.d000781 A d (_root_.GD.N0230.N0624.d000773 A hd) e he
  have havg : _root_.GD.N0230.N0624.d000774 A e = d :=
    hsym _ (_root_.GD.N0230.N0624.d000778 A e) havgDom

  have hnorm_le : ‖e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    have h := he θ₀
    rw [A.href, A.href] at h
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h
  have hvar := _root_.GD.N0230.N0624.d000782 (fun g => A.act g e)
  have hsumnorm : ∑ g : G, ‖A.act g e‖ ^ 2 = (Fintype.card G : ℝ) * ‖e‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun g _ => by rw [A.norm_map g e]), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have havg' : (Fintype.card G : ℝ)⁻¹ • ∑ g', A.act g' e = d := havg
  rw [hsumnorm, havg'] at hvar
  have hcardpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hsum_nonpos : ∑ g : G, ‖A.act g e - d‖ ^ 2 ≤ 0 := by
    rw [hvar]
    nlinarith [hnorm_le, hcardpos]
  have hsum_zero : ∑ g : G, ‖A.act g e - d‖ ^ 2 = 0 :=
    le_antisymm hsum_nonpos (Finset.sum_nonneg (fun g _ => sq_nonneg _))
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun g _ => sq_nonneg ‖A.act g e - d‖)).mp hsum_zero 1 (Finset.mem_univ _)
  have hone : A.act 1 e = d := by
    have h0 : ‖A.act 1 e - d‖ = 0 := by
      nlinarith [norm_nonneg (A.act 1 e - d)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  rw [A.act_one] at hone
  exact hone



theorem d000784
    (d : H) (hprof : _root_.GD.N0230.N0624.d000772 A d) :
    _root_.GD.N0230.N0608.d000674 risk d ↔
      _root_.GD.N0230.N0624.d000771 A d ∧
        ∀ e, _root_.GD.N0230.N0624.d000771 A e → _root_.GD.N0230.N0608.d000672 risk e d → e = d := by
  constructor
  · intro hterm
    exact ⟨_root_.GD.N0230.N0624.d000775 A d hprof hterm, fun e _ he => hterm e he⟩
  · rintro ⟨hd, hsym⟩
    exact _root_.GD.N0230.N0624.d000783 A d hd hsym

end N0624
end N0230
end GD

#print axioms _root_.GD.N0230.N0624.d000775
#print axioms _root_.GD.N0230.N0624.d000784
