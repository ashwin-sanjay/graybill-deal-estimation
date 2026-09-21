import GD.Module0918
import GD.Module0948
import GD.Module0969
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
































open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1029

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0633
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1065
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1201

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



instance : T2Space (_root_.GD.N0232.N0720.N1025.d014303 m n) :=
  (_root_.GD.N0230.N0633.d001198 (H := _root_.GD.N0232.N0720.N1025.d014302 m n)).symm.t2Space






theorem d015353
    (p q : _root_.GD.N0232.N0720.N1025.d014302 m n) (a b : ℝ) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦
        a * _root_.GD.N0232.N0720.N1214.d014265 m n p omega + b * _root_.GD.N0232.N0720.N1214.d014265 m n q omega := by
  filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 m n (a • p + b • q),
    _root_.GD.N0232.N0720.N1214.d014267 m n p,
    _root_.GD.N0232.N0720.N1214.d014267 m n q,
    Lp.coeFn_add (a • p) (b • q),
    Lp.coeFn_smul a p, Lp.coeFn_smul b q] with omega h0 hp hq hadd hsa hsb
  rw [h0, hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, ← hp, ← hq]




theorem d015354
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p q : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) (hq : q ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g (a • p + b • q)
        (_root_.GD.N0232.N0720.N1080.d014189 m n hm hn hp hq ha hb hab) =
      a • _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp +
        b • _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g q hq := by
  have hcombo := _root_.GD.N0232.N0720.N1029.d015353 m n p q a b

  have hcomboPull :
      _root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q) =ᵐ[_root_.GD.N0232.N0720.N1483.d014872 m n g]
        fun omega ↦
          a * _root_.GD.N0232.N0720.N1214.d014265 m n p omega +
            b * _root_.GD.N0232.N0720.N1214.d014265 m n q omega :=
    (_root_.GD.N0232.N0720.N1483.d014894 m n g).ae_le hcombo
  have hcomp :=
    (_root_.GD.N0232.N0720.N1483.d014875 m n g).quasiMeasurePreserving.ae_eq_comp
      hcomboPull

  have hraw :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q))
        =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦
        a * _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) omega +
          b * _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q) omega := by
    filter_upwards [hcomp] with omega homega
    show g • _root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q) (g⁻¹ • omega) = _
    have hval :
        _root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q) (g⁻¹ • omega) =
          a * _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega) +
            b * _root_.GD.N0232.N0720.N1214.d014265 m n q (g⁻¹ • omega) := homega
    rw [hval]
    show g.shift + g.d009239 *
        (a * _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega) +
          b * _root_.GD.N0232.N0720.N1214.d014265 m n q (g⁻¹ • omega)) =
      a * (g.shift + g.d009239 * _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega)) +
        b * (g.shift + g.d009239 * _root_.GD.N0232.N0720.N1214.d014265 m n q (g⁻¹ • omega))
    linear_combination g.shift * hab.symm

  have hPmem := _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp
  have hQmem := _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g q hq
  have hSmem :
      MemLp
        (a • _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) +
          b • _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q)) 2
        (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (hPmem.const_smul a).add (hQmem.const_smul b)
  calc
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g (a • p + b • q)
        (_root_.GD.N0232.N0720.N1080.d014189 m n hm hn hp hq ha hb hab) =
        MemLp.toLp
          (a • _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) +
            b • _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q)) hSmem := by
      unfold _root_.GD.N0232.N0720.N1215.d014289
      exact MemLp.toLp_congr _ hSmem hraw
    _ = a • _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp +
          b • _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g q hq := by
        unfold _root_.GD.N0232.N0720.N1215.d014289
        rw [MemLp.toLp_add (hPmem.const_smul a) (hQmem.const_smul b),
          MemLp.toLp_const_smul a hPmem, MemLp.toLp_const_smul b hQmem]





def d015355 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Set (_root_.GD.N0232.N0720.N1025.d014303 m n) :=
  Subtype.val ''
    {p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn | _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p}



theorem d015356 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    IsClosed (_root_.GD.N0232.N0720.N1029.d015355 m n hm hn g) := by
  haveI : CompactSpace (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :=
    isCompact_iff_compactSpace.mp (_root_.GD.N0232.N0720.N1025.d014311 m n hm hn)
  have hclosed :
      IsClosed {p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn |
        _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p} :=
    isClosed_eq (_root_.GD.N0232.N0720.N1483.d014904 m n hm hn g) continuous_id
  exact (hclosed.isCompact.image continuous_subtype_val).isClosed




def d015357 : Set (_root_.GD.N0232.N0720.N1025.d014302 m n) :=
  toWeakSpaceCLM ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) ⁻¹'
    (⋂ g : _root_.GD.N0232.N0720.N1025.d014301, _root_.GD.N0232.N0720.N1029.d015355 m n hm hn g)



theorem d015358 (d : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    d ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn ↔
      ∃ hd : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn,
        ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
          _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hd = d := by
  constructor
  · intro hmem
    have hall := Set.mem_iInter.1 hmem
    obtain ⟨p1, hp1fix, hp1val⟩ := hall 1
    have hweak : toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d ∈
        _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := by
      rw [show toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d =
          toWeakSpaceCLM ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d from rfl, ← hp1val]
      exact p1.2
    have hd : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
      have := (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn
        (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d)).1 hweak
      simpa using this
    refine ⟨hd, ?_⟩
    intro g
    obtain ⟨pg, hpgfix, hpgval⟩ := hall g
    have hpg : pg = ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d, hweak⟩ :=
      Subtype.ext hpgval
    rw [hpg] at hpgfix
    have hval := congrArg Subtype.val hpgfix
    rw [_root_.GD.N0232.N0720.N1025.d014317, _root_.GD.N0232.N0720.N1025.d014308] at hval
    have hinner :
        (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
            ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d, hweak⟩ =
          ⟨d, hd⟩ := by
      apply Subtype.ext
      rw [_root_.GD.N0232.N0720.N1025.d014309]
      simp
    rw [hinner] at hval
    have htransport :
        toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)
            (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hd) =
          toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d := hval
    exact (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).injective htransport
  · rintro ⟨hd, hfix⟩
    apply Set.mem_iInter.2
    intro g
    have hweak : toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d ∈
        _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      ⟨d, hd, rfl⟩
    refine ⟨⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d, hweak⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [_root_.GD.N0232.N0720.N1025.d014317, _root_.GD.N0232.N0720.N1025.d014308]
    have hinner :
        (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
            ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d, hweak⟩ =
          ⟨d, hd⟩ := by
      apply Subtype.ext
      rw [_root_.GD.N0232.N0720.N1025.d014309]
      simp
    rw [hinner]
    show toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)
        (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hd) = _
    rw [hfix g]


theorem d015359 :
    IsClosed (_root_.GD.N0232.N0720.N1029.d015357 m n hm hn) := by
  exact (isClosed_iInter (_root_.GD.N0232.N0720.N1029.d015356 m n hm hn)).preimage
    (toWeakSpaceCLM ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).continuous



theorem d015360 :
    (_root_.GD.N0232.N0720.N1029.d015357 m n hm hn).Nonempty := by
  obtain ⟨p, _, hfix⟩ :=
    _root_.GD.N0232.N0720.N1483.d014906 m n hm hn
  refine ⟨((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1, ?_⟩
  apply Set.mem_iInter.2
  intro g
  refine ⟨p, hfix g, ?_⟩
  show p.1 = toWeakSpaceCLM ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1
  rw [_root_.GD.N0232.N0720.N1025.d014309]
  rfl



theorem d015361 :
    Convex ℝ (_root_.GD.N0232.N0720.N1029.d015357 m n hm hn) := by
  intro x hx y hy a b ha hb hab
  rw [_root_.GD.N0232.N0720.N1029.d015358] at hx hy ⊢
  obtain ⟨hxc, hxfix⟩ := hx
  obtain ⟨hyc, hyfix⟩ := hy
  refine ⟨_root_.GD.N0232.N0720.N1080.d014189 m n hm hn hxc hyc ha hb hab, ?_⟩
  intro g
  rw [_root_.GD.N0232.N0720.N1029.d015354 m n hm hn g x y hxc hyc a b ha hb hab,
    hxfix g, hyfix g]




theorem d015362 :
    ∃ v ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
      ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - v‖ =
        ⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
          ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖ := by
  exact exists_norm_eq_iInf_of_complete_convex
    (_root_.GD.N0232.N0720.N1029.d015360 m n hm hn)
    ((_root_.GD.N0232.N0720.N1029.d015359 m n hm hn).isComplete)
    (_root_.GD.N0232.N0720.N1029.d015361 m n hm hn)
    (0 : _root_.GD.N0232.N0720.N1025.d014302 m n)


theorem d015363
    {v w : _root_.GD.N0232.N0720.N1025.d014302 m n}
    (hv : v ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn)
    (hw : w ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn)
    (hveq : ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - v‖ =
      ⨅ u : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - u‖)
    (hweq : ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖ =
      ⨅ u : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - u‖) :
    v = w := by
  have h1 :=
    (norm_eq_iInf_iff_real_inner_le_zero
      (_root_.GD.N0232.N0720.N1029.d015361 m n hm hn) hv).1 hveq w hw
  have h2 :=
    (norm_eq_iInf_iff_real_inner_le_zero
      (_root_.GD.N0232.N0720.N1029.d015361 m n hm hn) hw).1 hweq v hv
  have hvw : ‖v - w‖ ^ 2 ≤ 0 := by
    have hnorm := @norm_sub_sq_real (_root_.GD.N0232.N0720.N1025.d014302 m n) _ _ v w
    have e1 : ⟪(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - v, w - v⟫_ℝ =
        - ⟪v, w⟫_ℝ + ‖v‖ ^ 2 := by
      rw [zero_sub, inner_neg_left, inner_sub_right,
        real_inner_self_eq_norm_sq]
      ring
    have e2 : ⟪(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w, v - w⟫_ℝ =
        - ⟪w, v⟫_ℝ + ‖w‖ ^ 2 := by
      rw [zero_sub, inner_neg_left, inner_sub_right,
        real_inner_self_eq_norm_sq]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have hcomm : ⟪w, v⟫_ℝ = ⟪v, w⟫_ℝ := real_inner_comm v w
    rw [hcomm] at h2
    linarith
  have hzero : ‖v - w‖ = 0 := by
    have := sq_nonneg ‖v - w‖
    nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)


noncomputable def d015364 : _root_.GD.N0232.N0720.N1025.d014302 m n :=
  Classical.choose (_root_.GD.N0232.N0720.N1029.d015362 m n hm hn)

theorem d015365 :
    _root_.GD.N0232.N0720.N1029.d015364 m n hm hn ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn ∧
      ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - _root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ =
        ⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
          ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖ := by
  have hspec := Classical.choose_spec (_root_.GD.N0232.N0720.N1029.d015362 m n hm hn)
  exact ⟨hspec.1, hspec.2⟩

theorem d015366 :
    _root_.GD.N0232.N0720.N1029.d015364 m n hm hn ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
  obtain ⟨hd, _⟩ := (_root_.GD.N0232.N0720.N1029.d015358 m n hm hn
    (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)).1 (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).1
  exact hd


theorem d015367 :
    ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)
        (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn) =
      _root_.GD.N0232.N0720.N1029.d015364 m n hm hn := by
  obtain ⟨hd, hfix⟩ := (_root_.GD.N0232.N0720.N1029.d015358 m n hm hn
    (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)).1 (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).1
  exact hfix





theorem d015368 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro theta
  exact lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn theta)




theorem d015369
    (e : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn))
    (hfix : ∀ he : e ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn,
      ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g e he = e) :
    e = _root_.GD.N0232.N0720.N1029.d015364 m n hm hn := by
  have he : e ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn) hdom
  have heLocus : e ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn :=
    (_root_.GD.N0232.N0720.N1029.d015358 m n hm hn e).2 ⟨he, hfix he⟩

  have href := hdom _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  have hnormLe :
      ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - e‖ ^ 2 ≤
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - _root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp href
  have hnorm :
      ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - e‖ ≤
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - _root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ := by
    nlinarith [norm_nonneg ((0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - e),
      norm_nonneg
        ((0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - _root_.GD.N0232.N0720.N1029.d015364 m n hm hn)]

  have hbdd : BddBelow
      (Set.range fun w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn ↦
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖) := by
    refine ⟨0, ?_⟩
    rintro r ⟨w, rfl⟩
    exact norm_nonneg _
  have hle :
      (⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖) ≤
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - e‖ :=
    ciInf_le hbdd ⟨e, heLocus⟩
  have heq : ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - e‖ =
      ⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖ := by
    apply le_antisymm _ hle
    calc ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - e‖ ≤
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - _root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ := hnorm
      _ = ⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
          ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖ :=
        (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).2
  exact _root_.GD.N0232.N0720.N1029.d015363 m n hm hn heLocus
    (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).1 heq
    (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).2




theorem d015370 :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) := by
  intro g theta
  conv_lhs =>
    rw [← _root_.GD.N0232.N0720.N1029.d015367 m n hm hn g]
  rw [_root_.GD.N0232.N0720.N1215.d014290 m n hm hn g theta
    (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn)]


theorem d015371 :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) := by
  intro theta
  apply ne_top_of_le_ne_top _
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn theta)
  rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
  exact ENNReal.ofReal_ne_top


noncomputable def d015372 : _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := _root_.GD.N0232.N0720.N1029.d015364 m n hm hn
  finiteRisk := _root_.GD.N0232.N0720.N1029.d015371 m n hm hn
  riskCharacter := _root_.GD.N0232.N0720.N1029.d015370 m n hm hn

theorem d015373 :
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) :=
  _root_.GD.N0232.N0720.N1029.d015368 m n hm hn






theorem d015374
    (hgap : _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact
    (_root_.GD.N0232.N0720.N1201.d015341
      m n hm hn).2
    ⟨_root_.GD.N0232.N0720.N1029.d015372 m n hm hn,
      _root_.GD.N0232.N0720.N1029.d015373 m n hm hn, hgap⟩

end

end N1029
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1029.d015354
#print axioms _root_.GD.N0232.N0720.N1029.d015361
#print axioms _root_.GD.N0232.N0720.N1029.d015360
#print axioms _root_.GD.N0232.N0720.N1029.d015369
#print axioms _root_.GD.N0232.N0720.N1029.d015368
#print axioms _root_.GD.N0232.N0720.N1029.d015373
#print axioms _root_.GD.N0232.N0720.N1029.d015374
