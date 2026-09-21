import GD.Module0146
import GD.Module0147
import GD.Module0148
import GD.Module0097
import GD.Module0918



























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1066

noncomputable section

set_option linter.unusedSectionVars false

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0230.N0553
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0585
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0671
open _root_.GD.N0230.N0712
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn

noncomputable local instance : Nonempty _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨_root_.GD.N0232.N0720.N1080.d014169⟩


def d014320 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ENNReal :=
  _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)



theorem d014321 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta := by
  exact lt_of_le_of_lt bot_le
    (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn theta)

theorem d014322 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta ≠ 0 :=
  (_root_.GD.N0232.N0720.N1066.d014321 m n hm hn theta).ne'


theorem d014323 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta ≠ ⊤ := by
  unfold _root_.GD.N0232.N0720.N1066.d014320
  rw [_root_.GD.N0232.N0720.N1080.d014184 m n hm hn theta]
  exact ENNReal.ofReal_ne_top


def d014324
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ENNReal :=
  _root_.GD.N0232.N0720.N1025.d014305 m n theta d / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta



theorem d014325
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta d ≤ 1 := by
  have hdStrong := (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn d).1 hd
  have hle : _root_.GD.N0232.N0720.N1025.d014305 m n theta d ≤ _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta :=
    (hdStrong theta).trans
      (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn theta).le
  unfold _root_.GD.N0232.N0720.N1066.d014324
  calc
    _root_.GD.N0232.N0720.N1025.d014305 m n theta d / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta ≤
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta /
          _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta :=
      ENNReal.div_le_div_right hle _
    _ = 1 := ENNReal.div_self
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta)


theorem d014326
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta d ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (_root_.GD.N0232.N0720.N1066.d014325 m n hm hn theta hd)




def d014327
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  by
    classical
    exact if hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn then
      (_root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta d).toReal
    else 1

theorem d014328
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d := by
  by_cases hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · simp [_root_.GD.N0232.N0720.N1066.d014327, hd, ENNReal.toReal_nonneg]
  · simp [_root_.GD.N0232.N0720.N1066.d014327, hd]

theorem d014329
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d ≤ 1 := by
  by_cases hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · simp only [_root_.GD.N0232.N0720.N1066.d014327, hd, dite_true]
    have h := ENNReal.toReal_mono ENNReal.one_ne_top
      (_root_.GD.N0232.N0720.N1066.d014325 m n hm hn theta hd)
    simpa using h
  · simp [_root_.GD.N0232.N0720.N1066.d014327, hd]



def d014330 :
    _root_.GD.N0230.N0567.d001622 _root_.GD.N0232.N0720.N1080.d014168 (_root_.GD.N0232.N0720.N1025.d014303 m n)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) 0 1 where
  profile := _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
  mem_Icc := by
    intro theta d _hd
    exact ⟨_root_.GD.N0232.N0720.N1066.d014328 m n hm hn theta d,
      _root_.GD.N0232.N0720.N1066.d014329 m n hm hn theta d⟩



abbrev d014331 :=
  _root_.GD.N0230.N0567.d001625 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)


abbrev d014332 : _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ :=
  _root_.GD.N0230.N0567.d001636 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)



theorem d014333
    {X : Type*} [TopologicalSpace X]
    (f : X → ENNReal) (C : Set X)
    (hf : LowerSemicontinuous f)
    (hfinite : ∀ x ∈ C, f x ≠ ⊤) :
    LowerSemicontinuousOn (fun x ↦ (f x).toReal) C := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro b
  by_cases hb : 0 ≤ b
  · refine ⟨f ⁻¹' Set.Iic (ENNReal.ofReal b),
      hf.isClosed_preimage _, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hxC, hx⟩
      refine ⟨hxC, ?_⟩
      rw [← ENNReal.toReal_ofReal hb]
      exact (ENNReal.toReal_le_toReal
        (hfinite x hxC) ENNReal.ofReal_ne_top).1
          (by simpa [ENNReal.toReal_ofReal hb] using hx)
    · rintro ⟨hxC, hx⟩
      refine ⟨hxC, ?_⟩
      simpa [ENNReal.toReal_ofReal hb] using
        (ENNReal.toReal_le_toReal
          (hfinite x hxC) ENNReal.ofReal_ne_top).2 hx
  · refine ⟨∅, isClosed_empty, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic,
      Set.mem_empty_iff_false, and_false]
    constructor
    · rintro ⟨_hxC, hx⟩
      exact (not_le_of_gt (lt_of_not_ge hb))
        (ENNReal.toReal_nonneg.trans hx)
    · exact False.elim



theorem d014334 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    LowerSemicontinuous
      (_root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta) := by
  change LowerSemicontinuous
    (fun d : _root_.GD.N0232.N0720.N1025.d014303 m n ↦
      _root_.GD.N0230.N0712.d001258 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          theta.location d /
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta)
  exact _root_.GD.N0230.N0712.d001261
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
      theta.location (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)



theorem d014335 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  intro d hd
  have hreal : LowerSemicontinuousWithinAt
      (fun e ↦ (_root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta e).toReal)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) d :=
    (_root_.GD.N0232.N0720.N1066.d014333 m n hm hn
      (_root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1066.d014334 m n hm hn theta)
      (fun e he ↦ _root_.GD.N0232.N0720.N1066.d014326
        m n hm hn theta he)) d hd
  apply hreal.congr_of_eventuallyEq hd
  filter_upwards [self_mem_nhdsWithin] with e he
  simp [_root_.GD.N0232.N0720.N1066.d014327, he]



theorem d014336 :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact _root_.GD.N0230.N0567.d001640
    (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)
    (_root_.GD.N0232.N0720.N1066.d014335 m n hm hn)


theorem d014337 (p q : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm (_root_.GD.N0230.N0718.d001528 p q) =
      _root_.GD.N0230.N0718.d001528
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q) := by
  simp [_root_.GD.N0230.N0718.d001528]



theorem d014338
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) ≤
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q) / 2 := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq
      (by norm_num) (by norm_num) (by norm_num)
  let p' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p
  let q' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q
  have hpStrong : p' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn p).1 hp
  have hqStrong : q' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn q).1 hq
  have hdomFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
    exact ENNReal.ofReal_ne_top
  have hpFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta p' ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hpStrong theta)
  have hqFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta q' ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hqStrong theta)
  have hraw := _root_.GD.N0230.N0670.d001649
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
    theta.location p' q' hpFinite hqFinite
  have hrawLe' :
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          theta.location (_root_.GD.N0230.N0718.d001528 p' q')).toReal ≤
        ((_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
            theta.location p').toReal +
          (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
            theta.location q').toReal) / 2 := by
    have htaxNonnegative :
        0 ≤ (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
          (_root_.GD.N0230.N0670.d001646 p' q')).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hrawLe :
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 p' q')).toReal ≤
        ((_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal +
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal) / 2 := by
    simpa [_root_.GD.N0232.N0720.N1080.d014182] using hrawLe'
  have hcapReal : 0 < (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal :=
    ENNReal.toReal_pos
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta)
  simp only [_root_.GD.N0232.N0720.N1066.d014327, hp, hq, hmid, dite_true,
    _root_.GD.N0232.N0720.N1066.d014324, _root_.GD.N0232.N0720.N1025.d014305, ENNReal.toReal_div]
  rw [_root_.GD.N0232.N0720.N1066.d014337 m n hm hn p q]
  calc
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 p' q')).toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal ≤
        (((_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal +
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal) / 2) /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal :=
      div_le_div_of_nonneg_right hrawLe hcapReal.le
    _ = ((_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal +
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) / 2 := by
      field_simp [hcapReal.ne']



theorem d014339
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (k : _root_.GD.N0232.N0720.N1066.d014331 m n hm hn) :
    0 ≤ _root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) k p q := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq
      (by norm_num) (by norm_num) (by norm_num)
  exact _root_.GD.N0230.N0567.d001644
    (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) hp hq hmid
    (fun theta ↦ _root_.GD.N0232.N0720.N1066.d014338
      m n hm hn theta hp hq) k



theorem d014340 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014172 m n ≪ _root_.GD.N0232.N0720.N1080.d014171 m n theta := by
  simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
    (_root_.GD.N0232.N0720.d009063
      m n theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos).2





theorem d014341
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)
        (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta) p q =
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
          (_root_.GD.N0230.N0670.d001646
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p)
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q)) /
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq
      (by norm_num) (by norm_num) (by norm_num)
  let p' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p
  let q' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q
  have hpStrong : p' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn p).1 hp
  have hqStrong : q' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn q).1 hq
  have hdomFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
    exact ENNReal.ofReal_ne_top
  have hpFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta p' ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hpStrong theta)
  have hqFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta q' ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hqStrong theta)
  have hraw := _root_.GD.N0230.N0670.d001649
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
    theta.location p' q' hpFinite hqFinite
  have hcapReal : 0 < (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal :=
    ENNReal.toReal_pos
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta)
  unfold _root_.GD.N0230.N0567.d001641
  rw [_root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta hp,
    _root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta hq,
    _root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta hmid]
  change
    (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q) / 2 -
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) = _
  simp only [_root_.GD.N0232.N0720.N1066.d014327, hp, hq, hmid, dite_true,
    _root_.GD.N0232.N0720.N1066.d014324, _root_.GD.N0232.N0720.N1025.d014305, ENNReal.toReal_div]
  rw [_root_.GD.N0232.N0720.N1066.d014337 m n hm hn p q]
  change
    ((_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal +
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) / 2 -
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 p' q')).toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal =
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
        (_root_.GD.N0230.N0670.d001646 p' q')).toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal
  change
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 p' q')).toReal +
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
        (_root_.GD.N0230.N0670.d001646 p' q')).toReal =
      ((_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal +
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal) / 2 at hraw
  field_simp [hcapReal.ne']
  linarith





theorem d014342
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hzero : _root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)
      (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta) p q = 0) :
    p = q := by
  let p' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p
  let q' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q
  let tax : ENNReal :=
    _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
      (_root_.GD.N0230.N0670.d001646 p' q')
  have hnormalizedZero :
      (tax / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal = 0 := by
    rw [← _root_.GD.N0232.N0720.N1066.d014341
      m n hm hn theta hp hq]
    exact hzero
  rw [ENNReal.toReal_div] at hnormalizedZero
  have hcapReal : 0 < (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal :=
    ENNReal.toReal_pos
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta)
  have htaxRealZero : tax.toReal = 0 := by
    field_simp [hcapReal.ne'] at hnormalizedZero
    simpa using hnormalizedZero
  have hpStrong : p' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn p).1 hp
  have hqStrong : q' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn q).1 hq
  have hdomFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
    exact ENNReal.ofReal_ne_top
  have hpFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta p' ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hpStrong theta)
  have hqFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta q' ≠ ⊤ :=
    ne_top_of_le_ne_top hdomFinite (hqStrong theta)
  have htaxLe :
      tax ≤ ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p' +
        ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta q' := by
    have hidentity := _root_.GD.N0230.N0670.d001647
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
      theta.location p' q'
    change
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 p' q') + tax =
        ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p' +
          ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta q' at hidentity
    rw [← hidentity]
    exact le_add_left le_rfl
  have htaxFinite : tax ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ htaxLe
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpFinite,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqFinite⟩
  have htaxZero : tax = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff tax).1 htaxRealZero with h | h
    · exact h
    · exact (htaxFinite h).elim
  have hpqStrong : p' = q' :=
    _root_.GD.N0230.N0671.d001650
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
      (_root_.GD.N0232.N0720.N1066.d014340 m n hm hn theta)
      htaxZero
  exact (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm.injective hpqStrong



theorem d014343 (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d ≤ 1 := by
  unfold _root_.GD.N0232.N0720.N1066.d014332 _root_.GD.N0230.N0567.d001636
  apply ciSup_le
  intro theta
  exact _root_.GD.N0232.N0720.N1066.d014329 m n hm hn theta d



theorem d014344 (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    BddAbove
      (Set.range (fun theta ↦
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d)) := by
  refine ⟨1, ?_⟩
  rintro value ⟨theta, rfl⟩
  exact _root_.GD.N0232.N0720.N1066.d014329 m n hm hn theta d



theorem d014345
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∉ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d = 1 := by
  apply le_antisymm (_root_.GD.N0232.N0720.N1066.d014343 m n hm hn d)
  have hle :
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 d ≤
        _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d := by
    unfold _root_.GD.N0232.N0720.N1066.d014332 _root_.GD.N0230.N0567.d001636
    exact le_ciSup (_root_.GD.N0232.N0720.N1066.d014344 m n hm hn d)
      _root_.GD.N0232.N0720.N1080.d014169
  simpa [_root_.GD.N0232.N0720.N1066.d014327, hd] using hle


theorem d014346
    {e d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (he : e ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hed : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e d)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta e ≤
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d := by
  simp only [_root_.GD.N0232.N0720.N1066.d014327, he, hd, dite_true]
  apply ENNReal.toReal_mono
    (_root_.GD.N0232.N0720.N1066.d014326 m n hm hn theta hd)
  unfold _root_.GD.N0232.N0720.N1066.d014324
  exact ENNReal.div_le_div_right (hed theta) _



theorem d014347 :
    _root_.GD.N0230.N0585.d001305
      (_root_.GD.N0232.N0720.N1025.d014305 m n) (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) := by
  intro e d hed
  by_cases hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · have he : e ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      _root_.GD.N0232.N0720.N1025.d014314 m n hm hn hd hed
    unfold _root_.GD.N0232.N0720.N1066.d014332 _root_.GD.N0230.N0567.d001636
    apply ciSup_le
    intro theta
    calc
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta e ≤
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d :=
        _root_.GD.N0232.N0720.N1066.d014346
          m n hm hn he hd hed theta
      _ ≤ ⨆ eta, _root_.GD.N0232.N0720.N1066.d014327 m n hm hn eta d :=
        le_ciSup (_root_.GD.N0232.N0720.N1066.d014344 m n hm hn d) theta
  · rw [_root_.GD.N0232.N0720.N1066.d014345 m n hm hn hd]
    exact _root_.GD.N0232.N0720.N1066.d014343 m n hm hn e



theorem d014348
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014324 m n hm hn theta
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1066.d014324 m n hm hn
        (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta) p.1 := by
  let eta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g eta = theta := by
    simp [eta]
  have hmap :
      (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
        _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).2 := by
    simp [_root_.GD.N0232.N0720.N1025.d014316, _root_.GD.N0232.N0720.N1215.d014298]
  have hcore :
      _root_.GD.N0232.N0720.N1066.d014324 m n hm hn (_root_.GD.N0232.N0720.N1215.d014272 g eta)
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
        _root_.GD.N0232.N0720.N1066.d014324 m n hm hn eta p.1 := by
    unfold _root_.GD.N0232.N0720.N1066.d014324 _root_.GD.N0232.N0720.N1066.d014320 _root_.GD.N0232.N0720.N1025.d014305
    rw [hmap]
    change
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g eta)
          (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
            ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1
            ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).2) /
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g eta) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) =
        _root_.GD.N0232.N0720.N1080.d014182 m n eta ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1 /
          _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)
    rw [_root_.GD.N0232.N0720.N1215.d014290, _root_.GD.N0232.N0720.N1215.d014293]
    apply ENNReal.mul_div_mul_left
    · exact ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos g.d009240)
    · exact ENNReal.ofReal_ne_top
  simpa [heta, eta] using hcore


theorem d014349
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
        (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta) p.1 := by
  simp only [_root_.GD.N0232.N0720.N1066.d014327, p.2,
    (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).2, dite_true]
  rw [_root_.GD.N0232.N0720.N1066.d014348 m n hm hn g theta p]



theorem d014350
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1066.d014332 m n hm hn p.1 := by
  unfold _root_.GD.N0232.N0720.N1066.d014332 _root_.GD.N0230.N0567.d001636
  change
    (⨆ theta, _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta
      (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1) =
      ⨆ theta, _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p.1
  apply le_antisymm
  · apply ciSup_le
    intro theta
    rw [_root_.GD.N0232.N0720.N1066.d014349 m n hm hn g theta p]
    exact le_ciSup
      (_root_.GD.N0232.N0720.N1066.d014344 m n hm hn p.1)
      (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta)
  · apply ciSup_le
    intro eta
    have hle := le_ciSup
      (_root_.GD.N0232.N0720.N1066.d014344 m n hm hn
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1)
      (_root_.GD.N0232.N0720.N1215.d014272 g eta)
    rw [_root_.GD.N0232.N0720.N1066.d014349
      m n hm hn g (_root_.GD.N0232.N0720.N1215.d014272 g eta) p] at hle
    simpa using hle








theorem
    d014351
    (hfaithful : _root_.GD.N0230.N0553.d001612
      (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (y : ℝ) ↦ g • y) repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired <
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      (∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired) →
        ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] repaired) := by
  apply
    _root_.GD.N0232.N0720.N1025.d014319
      m n hm hn
      (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
  · exact _root_.GD.N0232.N0720.N1066.d014336 m n hm hn
  · intro d hd
    exact _root_.GD.N0230.N0567.d001639
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) hd
  · intro d _hd
    exact _root_.GD.N0230.N0567.d001634
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) d
  · intro p hp q hq k
    exact _root_.GD.N0230.N0567.d001642
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) k p q
  · intro p hp q hq k
    exact _root_.GD.N0232.N0720.N1066.d014339 m n hm hn hp hq k
  · exact hfaithful
  · exact _root_.GD.N0232.N0720.N1066.d014347 m n hm hn
  · intro g d
    exact _root_.GD.N0232.N0720.N1066.d014350 m n hm hn g d

end

end N1066
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1066.d014336
#print axioms _root_.GD.N0232.N0720.N1066.d014339
#print axioms _root_.GD.N0232.N0720.N1066.d014341
#print axioms _root_.GD.N0232.N0720.N1066.d014342
#print axioms _root_.GD.N0232.N0720.N1066.d014347
#print axioms _root_.GD.N0232.N0720.N1066.d014350
#print axioms _root_.GD.N0232.N0720.N1066.d014351
