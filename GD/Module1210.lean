import GD.Module1080
import GD.Module1204
import GD.Module1178
import GD.Module1209
import GD.Module1181

set_option warningAsError true























open MeasureTheory Set

namespace GD.N0232.N0720.N1150

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0232.N0720.N1065
open _root_.GD.N0232.N0720.N1063
open _root_.GD.N0232.N0720.N1077
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1147
open _root_.GD.N0232.N0720.N1149
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1472
open _root_.GD.N0232.N0720.N1475
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0232.N0720.N1505

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

abbrev d019557 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1029.d015364 m n hm hn

abbrev d019558 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn)



theorem d019559 :
    _root_.GD.N0232.N0720.N1150.d019558 m n hm hn ∈
      _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn) := by
  intro theta
  exact _root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn)

theorem d019560 :
    _root_.GD.N0232.N0720.N1150.d019558 m n hm hn ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
  intro theta
  exact (_root_.GD.N0232.N0720.N1150.d019559 m n hm hn theta).trans
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn theta)

theorem d019561 :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn) := by
  intro theta
  exact ne_top_of_le_ne_top
    (_root_.GD.N0232.N0720.N1029.d015371 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1150.d019559 m n hm hn theta)






theorem d019562
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hsummary : _root_.GD.N0232.N0720.N1468.d018955 m n p)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1468.d018955 m n (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp) := by
  obtain ⟨value, hvalue, hrep⟩ :=
    _root_.GD.N0232.N0720.N1501.d016306 m n p
  rw [hsummary] at hrep
  let transportedValue :
      _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ :=
    fun summary ↦ g • value (g⁻¹ • summary)
  have htransportedValue : Measurable transportedValue := by
    unfold transportedValue
    exact measurable_const.smul
      (hvalue.comp (measurable_const.smul measurable_id))
  have hcanonical :
      (fun omega ↦ _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp omega) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
    exact (_root_.GD.N0232.N0720.N1214.d014267 m n
      (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp)).symm.trans
        (_root_.GD.N0232.N0720.N1215.d014908 m n hm hn g p hp)
  have hdecisionRep :
      _root_.GD.N0232.N0720.N1214.d014265 m n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n :=
    (_root_.GD.N0232.N0720.N1214.d014267 m n p).trans hrep
  have htransportRep :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g (value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) :=
    _root_.GD.N0232.N0720.N1215.d014909 m n g hdecisionRep
  have hpointwise :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =
        transportedValue ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    funext omega
    unfold _root_.GD.N0232.N0720.N1214.d014261 transportedValue
    simp only [Function.comp_apply]
    rw [_root_.GD.N0232.N0720.N1475.d018975 m n
      (lt_of_lt_of_le (by omega) hm)
      (lt_of_lt_of_le (by omega) hn) g⁻¹ omega]
  have hfactor :
      (fun omega ↦ _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp omega) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014172 m n]
        transportedValue ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    exact hcanonical.trans (htransportRep.trans
      (Filter.Eventually.of_forall fun omega ↦ congrFun hpointwise omega))
  apply (_root_.GD.N0232.N0720.N1472.d019544 m n _).2
  have hstrong : StronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n]
      (transportedValue ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) :=
    (htransportedValue.comp
      (comap_measurable (_root_.GD.N0232.N0720.N1467.d012542 m n))).stronglyMeasurable
  exact hstrong.aestronglyMeasurable.congr hfactor.symm




def d019563 : Set (_root_.GD.N0232.N0720.N1025.d014302 m n) :=
  _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn) ∩
    {d | _root_.GD.N0232.N0720.N1468.d018955 m n d}

def d019564 : Set (_root_.GD.N0232.N0720.N1025.d014303 m n) :=
  toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) '' _root_.GD.N0232.N0720.N1150.d019563 m n hm hn

theorem d019565 :
    (_root_.GD.N0232.N0720.N1150.d019563 m n hm hn).Nonempty := by
  refine ⟨_root_.GD.N0232.N0720.N1150.d019558 m n hm hn,
    _root_.GD.N0232.N0720.N1150.d019559 m n hm hn, ?_⟩
  exact _root_.GD.N0232.N0720.N1468.d018951 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn)

theorem d019566 :
    Convex ℝ (_root_.GD.N0232.N0720.N1150.d019563 m n hm hn) := by
  intro x hx y hy a b ha hb hab
  change x ∈ _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn) ∧
    _root_.GD.N0232.N0720.N1468.d018955 m n x at hx
  change y ∈ _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn) ∧
    _root_.GD.N0232.N0720.N1468.d018955 m n y at hy
  change
    a • x + b • y ∈ _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn) ∧
      _root_.GD.N0232.N0720.N1468.d018955 m n (a • x + b • y)
  refine ⟨_root_.GD.N0232.N0720.N1159.d014632 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn)
    hx.1 hy.1 ha hb hab, ?_⟩
  unfold _root_.GD.N0232.N0720.N1468.d018955 at ⊢
  rw [map_add, map_smul, map_smul, hx.2, hy.2]

theorem d019567 :
    IsClosed (_root_.GD.N0232.N0720.N1150.d019563 m n hm hn) := by
  apply (_root_.GD.N0232.N0720.N1159.d014631 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn)).inter
  exact isClosed_eq (_root_.GD.N0232.N0720.N1501.d016291 m n).continuous continuous_id

theorem d019568
    {d : _root_.GD.N0232.N0720.N1025.d014302 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1150.d019563 m n hm hn) :
    ‖d‖ ≤ ‖_root_.GD.N0232.N0720.N1150.d019557 m n hm hn‖ :=
  _root_.GD.N0232.N0720.N1147.d017289 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn) d hd.1

theorem d019569 :
    IsCompact (_root_.GD.N0232.N0720.N1150.d019564 m n hm hn) := by
  exact _root_.GD.N0230.N0633.d001201
    ‖_root_.GD.N0232.N0720.N1150.d019557 m n hm hn‖
    (_root_.GD.N0232.N0720.N1150.d019566 m n hm hn)
    (_root_.GD.N0232.N0720.N1150.d019567 m n hm hn)
    (fun d hd ↦ _root_.GD.N0232.N0720.N1150.d019568
      m n hm hn hd)

theorem d019570 :
    Convex ℝ (_root_.GD.N0232.N0720.N1150.d019564 m n hm hn) := by
  exact (_root_.GD.N0232.N0720.N1150.d019566 m n hm hn).linear_image
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).toLinearMap

theorem d019571 :
    (_root_.GD.N0232.N0720.N1150.d019564 m n hm hn).Nonempty := by
  obtain ⟨d, hd⟩ := _root_.GD.N0232.N0720.N1150.d019565 m n hm hn
  exact ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d, d, hd, rfl⟩

theorem d019572 :
    _root_.GD.N0230.N0709.d001221 (_root_.GD.N0232.N0720.N1150.d019564 m n hm hn) := by
  unfold _root_.GD.N0230.N0709.d001221 _root_.GD.N0232.N0720.N1150.d019564
  have himage :
      (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm ''
          (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) ''
            _root_.GD.N0232.N0720.N1150.d019563 m n hm hn) =
        _root_.GD.N0232.N0720.N1150.d019563 m n hm hn := by
    ext d
    constructor
    · rintro ⟨w, ⟨e, he, rfl⟩, rfl⟩
      simpa using he
    · intro hd
      exact ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d,
        ⟨d, hd, rfl⟩, by simp⟩
  rw [himage, isBounded_iff_forall_norm_le]
  exact ⟨‖_root_.GD.N0232.N0720.N1150.d019557 m n hm hn‖,
    fun d hd ↦ _root_.GD.N0232.N0720.N1150.d019568
      m n hm hn hd⟩

theorem d019573 :
    _root_.GD.N0232.N0720.N1150.d019564 m n hm hn ⊆ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := by
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨d, _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n)
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn) hd.1, rfl⟩

theorem d019574
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
      (_root_.GD.N0232.N0720.N1150.d019564 m n hm hn)
      (_root_.GD.N0232.N0720.N1150.d019564 m n hm hn) := by
  rintro _ ⟨d, hd, rfl⟩
  have hdOuter : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn) hd.1
  have hweakOuter : toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d ∈
      _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := ⟨d, hdOuter, rfl⟩
  rw [_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hweakOuter]
  refine ⟨_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hdOuter, ⟨?_, ?_⟩, rfl⟩
  · intro eta
    let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
    have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
    rw [← heta,
      _root_.GD.N0232.N0720.N1215.d014290 m n hm hn g theta d hdOuter,
      _root_.GD.N0232.N0720.N1029.d015370 m n hm hn g theta]
    exact mul_le_mul_of_nonneg_left (hd.1 theta) bot_le
  · exact _root_.GD.N0232.N0720.N1150.d019562 m n hm hn hdOuter hd.2 g




theorem d019575 :
    ∃ r : _root_.GD.N0232.N0720.N1025.d014302 m n,
      r ∈ _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn) ∧
      _root_.GD.N0232.N0720.N1468.d018955 m n r ∧
      r ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn ∧
      ∀ hr : r ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn,
        ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
          _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g r hr = r := by
  let C := _root_.GD.N0232.N0720.N1150.d019564 m n hm hn
  let inner : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun t ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
  let outer : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun s ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
  have hCsubset : C ⊆ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1150.d019573 m n hm hn
  obtain ⟨x, hxC, hxinner, hxouter⟩ :=
    _root_.GD.N0230.N0710.d001248
      inner outer C
      (_root_.GD.N0232.N0720.N1150.d019569 m n hm hn)
      (_root_.GD.N0232.N0720.N1150.d019570 m n hm hn)
      (_root_.GD.N0232.N0720.N1150.d019571 m n hm hn)
      (_root_.GD.N0232.N0720.N1150.d019572 m n hm hn)
      (fun t ↦ _root_.GD.N0232.N0720.N1150.d019574 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t))
      (fun t ↦ (_root_.GD.N0232.N0720.N1483.d014905
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)).mono hCsubset)
      (fun t u hu v hv a b ha hb hab ↦
        _root_.GD.N0232.N0720.N1065.d014586 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
          (hCsubset hu) (hCsubset hv) ha hb hab)
      (_root_.GD.N0232.N0720.N1065.d014609 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014611 m n hm hn)
      (fun s ↦ _root_.GD.N0232.N0720.N1150.d019574 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s))
      (fun s ↦ (_root_.GD.N0232.N0720.N1483.d014905
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)).mono hCsubset)
      (fun s u hu v hv a b ha hb hab ↦
        _root_.GD.N0232.N0720.N1065.d014586 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
          (hCsubset hu) (hCsubset hv) ha hb hab)
      (_root_.GD.N0232.N0720.N1065.d014610 m n hm hn)
  have hxOuter : x ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := hCsubset hxC
  change x ∈ _root_.GD.N0232.N0720.N1150.d019564 m n hm hn at hxC
  obtain ⟨r, hrC, hrx⟩ := hxC
  subst x
  have hrOuter : r ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn) hrC.1
  refine ⟨r, hrC.1, hrC.2, hrOuter, ?_⟩
  intro hr g
  have hfactor := _root_.GD.N0232.N0720.N1065.d014606 g
  have hmul := _root_.GD.N0232.N0720.N1065.d014596 m n hm hn
    (_root_.GD.N0232.N0720.N1065.d014602 g.shift) (_root_.GD.N0232.N0720.N1065.d014603 g.logScale) hxOuter
  have hfixedAmbient :
      _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g
          (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r) =
        toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r := by
    rw [← hfactor, ← hmul]
    change inner g.shift
      (outer g.logScale (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r)) =
        toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r
    rw [hxouter g.logScale, hxinner g.shift]
  let w : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r, hxOuter⟩
  have hweakFixed : _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g w = w := by
    apply Subtype.ext
    change (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g w).1 =
      toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r
    rw [← _root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hxOuter]
    exact hfixedAmbient
  have hstrongFixed :
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm w) =
        (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm w := by
    apply (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).injective
    simpa only [_root_.GD.N0232.N0720.N1025.d014316, Function.comp_apply,
      Equiv.apply_symm_apply] using hweakFixed
  have hwStrong :
      (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm w = ⟨r, hrOuter⟩ := by
    apply Subtype.ext
    rfl
  rw [hwStrong] at hstrongFixed
  have hvalue := congrArg Subtype.val hstrongFixed
  have hcanonical :
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g r hrOuter = r := by
    simpa only [_root_.GD.N0232.N0720.N1215.d014298] using hvalue
  rw [show hr = hrOuter from Subsingleton.elim _ _]
  exact hcanonical




theorem d019576 :
    _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) =
      _root_.GD.N0232.N0720.N1029.d015364 m n hm hn := by
  obtain ⟨r, hrBelow, hrSummary, _hrOuter, hrFixed⟩ :=
    _root_.GD.N0232.N0720.N1150.d019575 m n hm hn
  have hrequal : r = _root_.GD.N0232.N0720.N1029.d015364 m n hm hn :=
    _root_.GD.N0232.N0720.N1029.d015369
      m n hm hn r hrBelow hrFixed
  rw [← hrequal]
  exact hrSummary





theorem d019577 :
    ∃ h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable h ∧
        _root_.GD.N0232.N0720.N1063.d019453
          (_root_.GD.N0232.N0720.N1029.d015364 2 2 (by omega) (by omega)) h := by
  apply
    _root_.GD.N0232.N0720.N1149.d019470
  exact _root_.GD.N0232.N0720.N1150.d019576 2 2 (by omega) (by omega)




theorem d019578
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn)) :
    _root_.GD.N0232.N0720.N1150.d019558 m n hm hn = _root_.GD.N0232.N0720.N1150.d019557 m n hm hn := by
  apply _root_.GD.N0232.N0720.N1029.d015369 m n hm hn
  · exact _root_.GD.N0232.N0720.N1150.d019559 m n hm hn
  · intro hlower g
    rw [_root_.GD.N0232.N0720.N1077.d018051 m n hm hn g
      (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn) hlower
      (_root_.GD.N0232.N0720.N1150.d019561 m n hm hn)]
    exact ((_root_.GD.N0232.N0720.N1159.d014655 m n hm hn
      (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn)
      (_root_.GD.N0232.N0720.N1150.d019561 m n hm hn)).2 hrep) g





theorem d019579 :
    _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1150.d019558 m n hm hn = _root_.GD.N0232.N0720.N1150.d019557 m n hm hn := by
  constructor
  · exact _root_.GD.N0232.N0720.N1150.d019578
      m n hm hn
  · intro heq
    rw [heq]
    exact _root_.GD.N0232.N0720.N1505.d018995
      m n hm hn






theorem d019580
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn)) :
    _root_.GD.N0232.N0720.N1150.d019558 m n hm hn = _root_.GD.N0232.N0720.N1150.d019557 m n hm hn := by
  have hnorm :
      ‖_root_.GD.N0232.N0720.N1150.d019558 m n hm hn‖ ^ 2 = ‖_root_.GD.N0232.N0720.N1150.d019557 m n hm hn‖ ^ 2 :=
    _root_.GD.N0232.N0720.N1147.d017296
      m n hm hn (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn)
      (_root_.GD.N0232.N0720.N1150.d019559 m n hm hn) hchar
  have hpyth := _root_.GD.N0232.N0720.N1468.d018952 m n (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn)
  have hzero :
      ‖_root_.GD.N0232.N0720.N1150.d019557 m n hm hn - _root_.GD.N0232.N0720.N1150.d019558 m n hm hn‖ = 0 := by
    change
      ‖_root_.GD.N0232.N0720.N1150.d019557 m n hm hn‖ ^ 2 =
        ‖_root_.GD.N0232.N0720.N1150.d019558 m n hm hn‖ ^ 2 +
          ‖_root_.GD.N0232.N0720.N1150.d019557 m n hm hn - _root_.GD.N0232.N0720.N1150.d019558 m n hm hn‖ ^ 2 at hpyth
    nlinarith [norm_nonneg
      (_root_.GD.N0232.N0720.N1150.d019557 m n hm hn - _root_.GD.N0232.N0720.N1150.d019558 m n hm hn)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

theorem d019581 :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1150.d019558 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1150.d019558 m n hm hn = _root_.GD.N0232.N0720.N1150.d019557 m n hm hn := by
  constructor
  · exact _root_.GD.N0232.N0720.N1150.d019580 m n hm hn
  · intro heq
    rw [heq]
    exact _root_.GD.N0232.N0720.N1029.d015370 m n hm hn

end

end GD.N0232.N0720.N1150

#print axioms _root_.GD.N0232.N0720.N1150.d019559
#print axioms _root_.GD.N0232.N0720.N1150.d019561
#print axioms _root_.GD.N0232.N0720.N1150.d019562
#print axioms _root_.GD.N0232.N0720.N1150.d019575
#print axioms _root_.GD.N0232.N0720.N1150.d019576
#print axioms _root_.GD.N0232.N0720.N1150.d019577
#print axioms _root_.GD.N0232.N0720.N1150.d019579
#print axioms _root_.GD.N0232.N0720.N1150.d019581
