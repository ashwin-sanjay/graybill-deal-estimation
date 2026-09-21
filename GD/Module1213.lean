import GD.Module0982
import GD.Module1212










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0720.N1223

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0611
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1258
open _root_.GD.N0232.N0720.N1506 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1295 _root_.GD.N0232.N0720.N1411
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1424
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1459 _root_.GD.N0232.N0720.N1467
open _root_.GD.N0107 _root_.GD.N0137

private theorem d019621 (m n : ℕ)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ⇑((Fintype.card (_root_.GD.N0232.N0720.N1506.d018997 m n) : ℝ)⁻¹ •
      ∑ g : _root_.GD.N0232.N0720.N1506.d018997 m n, _root_.GD.N0232.N0720.N1506.d019007 m n g (hmem.toLp d))
      =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1295.d019241 m n d := by
  classical
  have heach (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
      ⇑(_root_.GD.N0232.N0720.N1506.d019007 m n g (hmem.toLp d)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ d (_root_.GD.N0232.N0720.N1506.d018998 m n g omega) := by
    exact (Lp.coeFn_compMeasurePreserving _
      (_root_.GD.N0232.N0720.N1506.d019006 m n g)).trans
      ((_root_.GD.N0232.N0720.N1506.d019006 m n g).quasiMeasurePreserving.ae_eq_comp
        hmem.coeFn_toLp)
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [_root_.GD.N0232.N0720.N1506.d019012 m n Finset.univ
    (fun g : _root_.GD.N0232.N0720.N1506.d018997 m n ↦ _root_.GD.N0232.N0720.N1506.d019007 m n g (hmem.toLp d)),
    ae_all_iff.2 heach] with omega hsum heach
  simp only [Pi.smul_apply, smul_eq_mul, hsum, _root_.GD.N0232.N0720.N1295.d019241]
  congr 1
  exact Finset.sum_congr rfl (fun g _ ↦ heach g)


theorem d019622 (m n : ℕ) (C : ℝ)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1295.d019242 m n d) ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
  classical
  have hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hd
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound _root_.GD.N0232.N0720.N1080.d014169))
  let p := hmem.toLp d
  let q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (Fintype.card (_root_.GD.N0232.N0720.N1506.d018997 m n) : ℝ)⁻¹ •
      ∑ g : _root_.GD.N0232.N0720.N1506.d018997 m n, _root_.GD.N0232.N0720.N1506.d019007 m n g p
  have hq : q ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C := by
    intro theta
    have havg := _root_.GD.N0232.N0720.N1506.d019013 m n theta
      (fun g : _root_.GD.N0232.N0720.N1506.d018997 m n ↦ _root_.GD.N0232.N0720.N1506.d019007 m n g p)
    simp_rw [_root_.GD.N0232.N0720.N1506.d019011] at havg
    have hc : (Fintype.card (_root_.GD.N0232.N0720.N1506.d018997 m n) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := _root_.GD.N0232.N0720.N1506.d018997 m n)
    have hrisk : _root_.GD.N0232.N0720.N1080.d014182 m n theta q ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
      simpa only [q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← mul_assoc, ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _), one_mul] using havg
    exact hrisk.trans ((_root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem) ▸ hbound theta)
  have hqraw : ⇑q =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1295.d019241 m n d :=
    _root_.GD.N0232.N0720.N1223.d019621 m n d hmem
  have hreflect : _root_.GD.N0232.N0720.N1446.d019032 m n q ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C := by
    intro theta
    rw [_root_.GD.N0232.N0720.N1446.d019037]
    simpa only [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0232.N0720.N1446.d019026, _root_.GD.N0232.N0720.N1446.d019027]
      using hq (_root_.GD.N0232.N0720.N1446.d019024 theta)
  let r := (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • _root_.GD.N0232.N0720.N1446.d019032 m n q
  have hr : r ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C :=
    _root_.GD.N0232.N0720.N1257.d015515 m n C hq hreflect (by norm_num) (by norm_num) (by norm_num)
  have hreflectRaw : ⇑(_root_.GD.N0232.N0720.N1446.d019032 m n q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦ -_root_.GD.N0232.N0720.N1295.d019241 m n d (_root_.GD.N0232.N0720.N1446.d019019 m n omega) := by
    refine (Lp.coeFn_neg _).trans ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving q
      (_root_.GD.N0232.N0720.N1446.d019031 m n),
      (_root_.GD.N0232.N0720.N1446.d019031 m n).quasiMeasurePreserving.ae_eq_comp hqraw]
      with omega hcomp hraw
    simp only [Pi.neg_apply, hcomp]
    exact congrArg (fun x : ℝ ↦ -x) hraw
  have hrraw : ⇑r =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1295.d019242 m n d := by
    filter_upwards [Lp.coeFn_add ((1 / 2 : ℝ) • q)
      ((1 / 2 : ℝ) • _root_.GD.N0232.N0720.N1446.d019032 m n q),
      Lp.coeFn_smul (1 / 2 : ℝ) q,
      Lp.coeFn_smul (1 / 2 : ℝ) (_root_.GD.N0232.N0720.N1446.d019032 m n q), hqraw, hreflectRaw]
      with omega hadd hleft hright hq hreflect
    simp only [r, hadd, Pi.add_apply, hleft, hright, Pi.smul_apply, smul_eq_mul,
      hq, hreflect, _root_.GD.N0232.N0720.N1295.d019242]
    ring
  intro theta
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta
    ((_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
      (hrraw.symm.trans (_root_.GD.N0232.N0720.N1214.d014267 m n r).symm)),
      _root_.GD.N0232.N0720.N1215.d014286]
  exact hr theta

theorem d019623 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1257.d015508 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t) = t.1 * (1 - t.1) := by
  have ht : t.1 ≠ 0 := ne_of_gt t.2.1
  have ht' : 1 - t.1 ≠ 0 := ne_of_gt (sub_pos.mpr t.2.2)
  unfold _root_.GD.N0232.N0720.N1257.d015508 _root_.GD.N0232.N0720.N1398.d019614 _root_.GD.N0232.N0720.N1424.d014846 _root_.GD.N0232.N0720.N1424.d014847
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) (sub_nonneg.mpr t.2.2.le)),
    Real.sq_sqrt (mul_nonneg (by norm_num) t.2.1.le)]
  norm_num
  have hsum : (2 : ℝ) / (2 * (1 - t.1)) + 2 / (2 * t.1) =
      (t.1 * (1 - t.1))⁻¹ := by
    field_simp [ht, ht']
    ring
  rw [hsum, inv_inv]



theorem d019624 (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 2 2 theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 2 2 theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 t) ≤ C * t.1 * (1 - t.1) := by
  obtain ⟨e, he, hequiv, heb⟩ := _root_.GD.N0232.N0720.N1258.d015544
    2 2 (by omega) (by omega) C hC d hd hbound
  have hcov : _root_.GD.N0232.N0720.N1295.d019239 2 2 e := (_root_.GD.N0232.N0720.N1295.d019240 2 2 e).2 hequiv
  have hsym := _root_.GD.N0232.N0720.N1223.d019622 2 2 C e he heb
  have hae (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1295.d019242 2 2 e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 theta]
        _root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1411.d019271 e) := by
    have hpos : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta,
        0 < _root_.GD.N0107.d009085 omega.1 / 2 + _root_.GD.N0107.d009085 omega.2 / 2 := by
      have href := _root_.GD.N0232.N0720.N1459.d018933 2 2 (by omega) (by omega)
      apply (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta).ae_le
      filter_upwards [href] with omega homega
      simpa only [_root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548,
        Nat.cast_ofNat] using homega
    filter_upwards [hpos] with omega hpos
    exact _root_.GD.N0232.N0720.N1411.d019273 hcov omega hpos
  let g := _root_.GD.N0232.N0720.N1398.d019601 e
  have hg : Measurable g := _root_.GD.N0232.N0720.N1398.d019602 he
  have hgb : ∀ z, g z ∈ Icc (0 : ℝ) 1 := _root_.GD.N0232.N0720.N1398.d019603 e
  have hcap (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 2 2 theta (_root_.GD.N0232.N0720.N1425.d014719 2 2 g) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 2 2 theta) := by
    have hrisk := _root_.GD.N0232.N0720.N1159.d014662 2 2 theta (hae theta)
    have hfinite : _root_.GD.N0232.N0720.N1080.d014197 2 2 theta
        (_root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1411.d019271 e)) ≠ ⊤ := by
      rw [← hrisk]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsym theta)
    have hclip := _root_.GD.N0232.N0720.N1398.d019600 2 2 (by omega) (by omega)
      theta (_root_.GD.N0232.N0720.N1411.d019272 he) hfinite
    exact hclip.trans (hrisk ▸ hsym theta)
  refine ⟨g, hg, hgb, ?_⟩
  intro t
  have hb := hcap (_root_.GD.N0232.N0720.N1398.d019614 t)
  rw [_root_.GD.N0232.N0720.N1398.d019612 _ hg hgb,
    _root_.GD.N0232.N0720.N1398.d019615, _root_.GD.N0232.N0720.N1398.d019616, one_mul] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (_root_.GD.N0232.N0720.N1257.d015509 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t)))).mp hb
  have hnonneg : 0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t))
      (_root_.GD.N0107.d012732 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t).location
        (_root_.GD.N0107.d009046 2 2
          (_root_.GD.N0232.N0720.N1398.d019614 t).scale₁ (_root_.GD.N0232.N0720.N1398.d019614 t).scale₂)) := by
    unfold _root_.GD.N0141.d006684
    exact integral_nonneg (fun _ ↦ sq_nonneg _)
  rw [_root_.GD.N0232.N0720.N1398.d019616] at hnonneg
  rw [_root_.GD.N0232.N0720.N1223.d019623] at hb'
  change _root_.GD.N0232.N0720.N1398.d019610 g t.1 ≤ _
  nlinarith


theorem d019625
    (hred : ∀ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ), Measurable g →
      (∀ z, g z ∈ Icc (0 : ℝ) 1) → ∀ C : ℝ,
      ¬ (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 t) ≤ C * t.1 * (1 - t.1))) :
    _root_.GD.N0232.N0720.N1256.d015549 2 2 = ⊤ := by
  by_contra hfinite
  obtain ⟨e, he, heq⟩ :=
    _root_.GD.N0232.N0720.N1222.d015570
      2 2 (by omega) (by omega)
  let C := (_root_.GD.N0232.N0720.N1256.d015549 2 2).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015549 2 2 := ENNReal.ofReal_toReal hfinite
  have hbound (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 2 2 theta e ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 2 2 theta) := by
    apply (_root_.GD.N0232.N0720.N1256.d015553 2 2 (by omega) C hC theta e).mp
    rw [hval, ← heq]
    exact le_iSup (fun eta ↦ _root_.GD.N0232.N0720.N1256.d015547 2 2 eta e) theta
  obtain ⟨g, hg, hb, hcap⟩ := _root_.GD.N0232.N0720.N1223.d019624 C hC e he.1.1 hbound
  exact hred g hg hb C hcap

end
end GD.N0232.N0720.N1223
