import GD.Module1202
import GD.Module1192
import GD.Module1198
import GD.Module1182















open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1472

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0107
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1216
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1471
open _root_.GD.N0232.N0720.N1476
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1506

variable (m n : ℕ)





abbrev d019541 :=
  _root_.GD.N0232.N0720.N1476.d019350

@[fun_prop]
theorem d019542 : Measurable _root_.GD.N0232.N0720.N1472.d019541 := by
  exact
    _root_.GD.N0232.N0720.N1476.d019357



theorem d019543
    (hm : 2 ≤ m) (hn : 2 ≤ n) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1467.d012542 m n (_root_.GD.N0232.N0720.N1446.d019019 m n omega) =
      _root_.GD.N0232.N0720.N1472.d019541 (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := by
  exact
    _root_.GD.N0232.N0720.N1476.d019375
      m n (by omega) (by omega) omega



theorem d019544
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1468.d018955 m n d ↔
      AEStronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n]
        (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  constructor
  · intro hfixed
    rw [← hfixed]
    exact _root_.GD.N0232.N0720.N1501.d016293 m n d
  · intro hmeas
    let S := lpMeas ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016287 m n) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)
    letI : Fact (_root_.GD.N0232.N0720.N1501.d016287 m n ≤
        (inferInstance : MeasurableSpace (_root_.GD.N0232.N0720.N1080.d014170 m n))) :=
      ⟨_root_.GD.N0232.N0720.N1501.d016290 m n⟩
    have hmem : d ∈ S :=
      mem_lpMeas_iff_aestronglyMeasurable.mpr hmeas
    simpa [_root_.GD.N0232.N0720.N1468.d018955, S, _root_.GD.N0232.N0720.N1501.d016291, condExpL2] using
      (S.starProjection_eq_self_iff.mpr hmem)





theorem d019545
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hd : _root_.GD.N0232.N0720.N1468.d018955 m n d) :
    _root_.GD.N0232.N0720.N1468.d018955 m n (_root_.GD.N0232.N0720.N1446.d019032 m n d) := by
  obtain ⟨g, hg, hae⟩ :=
    _root_.GD.N0232.N0720.N1501.d016306 m n d
  rw [hd] at hae
  let h : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ :=
    fun s ↦ -g (_root_.GD.N0232.N0720.N1472.d019541 s)
  have hh : Measurable h := by
    exact hg.neg.comp _root_.GD.N0232.N0720.N1472.d019542
  have hpres := _root_.GD.N0232.N0720.N1446.d019031 m n
  have haeMap :
      (fun omega ↦ d omega) =ᵐ[(_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1446.d019019 m n)]
        g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    rw [hpres.map_eq]
    exact hae
  have haeComp := MeasureTheory.ae_eq_comp
    (_root_.GD.N0232.N0720.N1446.d019021 m n).aemeasurable haeMap
  have hreflect :
      (fun omega ↦ _root_.GD.N0232.N0720.N1446.d019032 m n d omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ -(d (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) := by
    unfold _root_.GD.N0232.N0720.N1446.d019032
    refine (Lp.coeFn_neg _).trans ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving d hpres] with omega homega
    simpa only [Pi.neg_apply, Function.comp_apply] using congrArg Neg.neg homega
  have hfactor :
      (fun omega ↦ _root_.GD.N0232.N0720.N1446.d019032 m n d omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        h ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    filter_upwards [hreflect, haeComp] with omega hr hq
    rw [hr]
    have hq' : d (_root_.GD.N0232.N0720.N1446.d019019 m n omega) =
        g (_root_.GD.N0232.N0720.N1467.d012542 m n (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) := by
      simpa only [Function.comp_apply] using hq
    rw [hq']
    simp only [Function.comp_apply, h, _root_.GD.N0232.N0720.N1472.d019543 m n hm hn]
  apply (_root_.GD.N0232.N0720.N1472.d019544 m n _).2
  have hstrong : StronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n]
      (h ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) :=
    (hh.comp (comap_measurable (_root_.GD.N0232.N0720.N1467.d012542 m n))).stronglyMeasurable
  exact hstrong.aestronglyMeasurable.congr hfactor.symm


theorem d019546
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (he : _root_.GD.N0232.N0720.N1468.d018955 m n e) :
    _root_.GD.N0232.N0720.N1468.d018955 m n
      ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) := by
  unfold _root_.GD.N0232.N0720.N1468.d018955 at he ⊢
  rw [map_smul, map_add, he]
  rw [_root_.GD.N0232.N0720.N1472.d019545 m n hm hn he]



def d019547
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ _root_.GD.N0232.N0720.N1446.d019032 m n e = e ∧
      _root_.GD.N0232.N0720.N1468.d018953 m n e d



def d019548
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    _root_.GD.N0232.N0720.N1446.d019032 m n e = e ∧
      _root_.GD.N0232.N0720.N1468.d018953 m n (_root_.GD.N0232.N0720.N1501.d016291 m n e) d



theorem d019549
    (d e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hprofile : ∀ theta,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) d = _root_.GD.N0232.N0720.N1080.d014182 m n theta d)
    (he : _root_.GD.N0230.N0608.d000672
      (_root_.GD.N0232.N0720.N1080.d014182 m n) e d) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) d := by
  intro theta
  have havg := _root_.GD.N0232.N0720.N1506.d019013
    m n (G := Fin 2) theta
    ![e, _root_.GD.N0232.N0720.N1446.d019032 m n e]
  simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.cast_ofNat] at havg
  have hreflect :
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1446.d019032 m n e) ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta d := by
    rw [_root_.GD.N0232.N0720.N1446.d019037]
    exact (he (_root_.GD.N0232.N0720.N1446.d019024 theta)).trans (le_of_eq (hprofile theta))
  calc
    _root_.GD.N0232.N0720.N1080.d014182 m n theta ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) ≤
        (2 : ℝ≥0∞)⁻¹ *
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta e +
            _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1446.d019032 m n e)) := havg
    _ ≤ (2 : ℝ≥0∞)⁻¹ *
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta d + _root_.GD.N0232.N0720.N1080.d014182 m n theta d) :=
      mul_le_mul_right (add_le_add (he theta) hreflect) _
    _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta d := by
      rw [← two_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]



theorem d019550
    (d e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfinite : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤)
    (hprofile : ∀ theta,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) d = _root_.GD.N0232.N0720.N1080.d014182 m n theta d)
    (he : _root_.GD.N0232.N0720.N1468.d018953 m n e d) :
    _root_.GD.N0232.N0720.N1468.d018953 m n
      ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) d := by
  refine ⟨_root_.GD.N0232.N0720.N1472.d019549 m n d e hprofile he.1, ?_⟩
  obtain ⟨theta, hstrict⟩ := he.2
  refine ⟨theta, ?_⟩
  have havg := _root_.GD.N0232.N0720.N1506.d019013
    m n (G := Fin 2) theta
    ![e, _root_.GD.N0232.N0720.N1446.d019032 m n e]
  simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.cast_ofNat] at havg
  have hreflect :
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1446.d019032 m n e) ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta d := by
    rw [_root_.GD.N0232.N0720.N1446.d019037]
    exact (he.1 (_root_.GD.N0232.N0720.N1446.d019024 theta)).trans (le_of_eq (hprofile theta))
  have hreflectFinite :
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1446.d019032 m n e) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfinite theta) hreflect
  have hadd :
      _root_.GD.N0232.N0720.N1080.d014182 m n theta e + _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1446.d019032 m n e) <
        _root_.GD.N0232.N0720.N1080.d014182 m n theta d + _root_.GD.N0232.N0720.N1080.d014182 m n theta d :=
    ENNReal.add_lt_add_of_lt_of_le hreflectFinite hstrict hreflect
  have hmul :
      (2 : ℝ≥0∞)⁻¹ *
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta e + _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1446.d019032 m n e)) <
        (2 : ℝ≥0∞)⁻¹ *
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta d + _root_.GD.N0232.N0720.N1080.d014182 m n theta d) := by
    exact ENNReal.mul_lt_mul_right
      (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
      (ENNReal.inv_ne_top.mpr (by norm_num)) hadd
  refine lt_of_le_of_lt havg ?_
  convert hmul using 1
  rw [← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]


theorem d019551
    (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1446.d019032 m n
        ((2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)) =
      (2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e) := by
  rw [_root_.GD.N0232.N0720.N1446.d019035, _root_.GD.N0232.N0720.N1446.d019034,
    _root_.GD.N0232.N0720.N1446.d019033, add_comm]








theorem d019552
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfinite : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤)
    (hprofile : ∀ theta,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) d = _root_.GD.N0232.N0720.N1080.d014182 m n theta d) :
    (∃ e, _root_.GD.N0232.N0720.N1468.d018953 m n e d) ↔
      _root_.GD.N0232.N0720.N1472.d019548 m n d := by
  constructor
  · rintro ⟨e, he⟩
    let mid : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
      (2 : ℝ)⁻¹ • (e + _root_.GD.N0232.N0720.N1446.d019032 m n e)
    have hmid : _root_.GD.N0232.N0720.N1468.d018953 m n mid d := by
      exact _root_.GD.N0232.N0720.N1472.d019550 m n d e hfinite hprofile he
    refine ⟨mid, ?_, _root_.GD.N0232.N0720.N1468.d018959 m n hm hn hmid⟩
    exact _root_.GD.N0232.N0720.N1472.d019551 m n e
  · rintro ⟨e, _heFixed, he⟩
    exact ⟨_root_.GD.N0232.N0720.N1501.d016291 m n e, he⟩








theorem d019553
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfinite : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤)
    (hprofile : ∀ theta,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) d = _root_.GD.N0232.N0720.N1080.d014182 m n theta d) :
    (∃ e, _root_.GD.N0232.N0720.N1468.d018953 m n e d) ↔
      _root_.GD.N0232.N0720.N1472.d019547 m n d := by
  constructor
  · rintro ⟨e, he⟩
    let q := _root_.GD.N0232.N0720.N1501.d016291 m n e
    have hqSummary : _root_.GD.N0232.N0720.N1468.d018955 m n q := by
      exact _root_.GD.N0232.N0720.N1468.d018951 m n e
    have hqStrict : _root_.GD.N0232.N0720.N1468.d018953 m n q d := by
      exact _root_.GD.N0232.N0720.N1468.d018959 m n hm hn he
    let mid : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
      (2 : ℝ)⁻¹ • (q + _root_.GD.N0232.N0720.N1446.d019032 m n q)
    refine ⟨mid, ?_, ?_, ?_⟩
    · exact _root_.GD.N0232.N0720.N1472.d019546 m n hm hn hqSummary
    · exact _root_.GD.N0232.N0720.N1472.d019551 m n q
    · exact _root_.GD.N0232.N0720.N1472.d019550
        m n d q hfinite hprofile hqStrict
  · rintro ⟨e, _heSummary, _heReflection, he⟩
    exact ⟨e, he⟩




theorem d019554
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1471.d019427 m n s ↔
      _root_.GD.N0232.N0720.N1472.d019548 m n s.value := by
  unfold _root_.GD.N0232.N0720.N1471.d019427
  exact _root_.GD.N0232.N0720.N1472.d019552
    m n hm hn s.value s.finiteRisk
      (_root_.GD.N0232.N0720.N1446.d019039 m n s)




theorem d019555
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1471.d019427 m n s ↔
      _root_.GD.N0232.N0720.N1472.d019547 m n s.value := by
  unfold _root_.GD.N0232.N0720.N1471.d019427
  exact _root_.GD.N0232.N0720.N1472.d019553
    m n hm hn s.value s.finiteRisk
      (_root_.GD.N0232.N0720.N1446.d019039 m n s)





theorem d019556
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1471.d019425 m n hm hn s ∧
          ¬ _root_.GD.N0232.N0720.N1472.d019547 m n s.value := by
  rw [_root_.GD.N0232.N0720.N1471.d019438
    m n hm hn]
  apply exists_congr
  intro s
  rw [and_congr_right_iff]
  intro _hstrict
  exact not_congr
    (_root_.GD.N0232.N0720.N1472.d019555
      m n hm hn s)

end

end N1472
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1472.d019550
#print axioms _root_.GD.N0232.N0720.N1472.d019552
#print axioms _root_.GD.N0232.N0720.N1472.d019554
#print axioms _root_.GD.N0232.N0720.N1472.d019545
#print axioms _root_.GD.N0232.N0720.N1472.d019553
#print axioms _root_.GD.N0232.N0720.N1472.d019555
#print axioms _root_.GD.N0232.N0720.N1472.d019556
