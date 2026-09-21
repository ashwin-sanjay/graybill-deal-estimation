import GD.Module1642
import GD.Module0980
import GD.Module1215

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0024.N0271

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1295
open _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1467 _root_.GD.N0232.N0720.N1497
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N1010
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0076.N0310.N0759
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1506 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1476
open _root_.GD.N0232.N0720.N1209 _root_.GD.N0232.N0720.N1342
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1286
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425

theorem d028028
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (hcov : _root_.GD.N0232.N0720.N1295.d019239 m n d) :
    ∃ q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable q ∧ _root_.GD.N0232.N0719.N0860.d011447 q ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n θ d := by
  let f := d ∘ _root_.GD.N0232.N0720.N1467.d012540 m n
  have hmem (θ : _root_.GD.N0232.N0720.N1080.d014168) : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by
    letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by unfold _root_.GD.N0232.N0720.N1080.d014171; infer_instance
    have herr := _root_.GD.N0232.N0720.N1396.d014784 m n θ hd.1 (hd.2 θ)
    convert herr.add
      (memLp_const θ.location : MemLp (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n => θ.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n θ)) using 1
    funext x
    exact (sub_add_cancel (d x) θ.location).symm
  have hf (θ : _root_.GD.N0232.N0719.N0859.d010809 2) :
      MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812
        2 (_root_.GD.N0232.N0720.N1467.d012537 m n) θ) := by
    let η : _root_.GD.N0232.N0720.N1080.d014168 := ⟨θ.location, θ.scale 0, θ.scale 1, θ.scale_pos 0, θ.scale_pos 1⟩
    have hscale : ![θ.scale 0, θ.scale 1] = θ.scale := by
      funext i
      fin_cases i <;> rfl
    have hmp := _root_.GD.N0232.N0720.N1497.d012550
      m n θ.location (θ.scale 0) (θ.scale 1)
    rw [hscale] at hmp
    exact (hmem η).comp_measurePreserving hmp
  have hfcov (b a : ℝ) (ha : 0 < a)
      (x : _root_.GD.N0232.N0719.N0900.d009094 2 (_root_.GD.N0232.N0720.N1467.d012537 m n)) :
      f (_root_.GD.N0232.N0719.N0900.d009095 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) b a x) =
        b + a * f x := by
    have hcarrier : _root_.GD.N0232.N0720.N1467.d012540 m n
        (_root_.GD.N0232.N0719.N0900.d009095 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) b a x) =
        _root_.GD.N0107.d009024 m n b a a (_root_.GD.N0232.N0720.N1467.d012540 m n x) := by
      rfl
    dsimp only [f, Function.comp_apply]
    rw [hcarrier]
    exact hcov b a _ ha
  obtain ⟨q, hq, hqcov, hqrisks⟩ := _root_.GD.N0024.N0272.d028027
    2 (_root_.GD.N0232.N0720.N1467.d012537 m n) (by omega) (_root_.GD.N0076.N0310.N0759.d014241 m n hm hn) f hf hfcov
  refine ⟨q, hq, ?_, fun θ => ?_⟩
  · intro b a ha s
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, Real.log a⟩
    have h := hqcov g s
    simpa only [g, _root_.GD.N0232.N0719.N1010.d011416, _root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0719.N0946.d009229.d009239,
      Real.exp_log ha] using h
  · have h := hqrisks (_root_.GD.N0076.N0310.N0759.d014240 θ)
    rw [← _root_.GD.N0076.N0310.N0759.d014243 m n θ (q ∘ _root_.GD.N0232.N0719.N0900.d009104
      2 (_root_.GD.N0232.N0720.N1467.d012537 m n)), ← _root_.GD.N0076.N0310.N0759.d014243 m n θ f] at h
    simpa only [f, Function.comp_def, _root_.GD.N0232.N0720.N1467.d012549,
      _root_.GD.N0232.N0720.N1467.d012542] using h

theorem d028029
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (hcov : _root_.GD.N0232.N0720.N1295.d019239 m n d)
    (B : _root_.GD.N0232.N0720.N1080.d014168 → ℝ≥0∞) (hBfinite : ∀ θ, B θ ≠ ⊤)
    (hBreflection : ∀ θ, B (_root_.GD.N0232.N0720.N1446.d019024 θ) = B θ)
    (hbound : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ B θ) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable g ∧ (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤ B θ := by
  obtain ⟨q, hq, hqaff, hqbound⟩ := _root_.GD.N0024.N0271.d028028 m n hm hn d hd hcov
  let f := q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n
  have hf : Measurable f := hq.comp (_root_.GD.N0232.N0720.N1501.d016289 m n)
  have hfb (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤ B θ :=
    (hqbound θ).trans (hbound θ)
  have hmem := _root_.GD.N0232.N0720.N1215.d014285 m n f hf
    (ne_top_of_le_ne_top (hBfinite _root_.GD.N0232.N0720.N1080.d014169) (hfb _root_.GD.N0232.N0720.N1080.d014169))
  let p := hmem.toLp f
  let r := (2 : ℝ)⁻¹ • (p + _root_.GD.N0232.N0720.N1446.d019032 m n p)
  let qR := _root_.GD.N0232.N0720.N1476.d019361 q
  have hpRisk (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ B θ := by
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ f hmem]
    exact hfb θ
  have hrRisk (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014182 m n θ r ≤ B θ := by
    have havg := _root_.GD.N0232.N0720.N1506.d019013 m n (G := Fin 2) θ ![p, _root_.GD.N0232.N0720.N1446.d019032 m n p]
    simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.cast_ofNat] at havg
    have hrefl : _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1446.d019032 m n p) ≤ B θ := by
      rw [_root_.GD.N0232.N0720.N1446.d019037]
      exact (hpRisk (_root_.GD.N0232.N0720.N1446.d019024 θ)).trans_eq (hBreflection θ)
    calc
      _root_.GD.N0232.N0720.N1080.d014182 m n θ r ≤ (2 : ℝ≥0∞)⁻¹ *
          (_root_.GD.N0232.N0720.N1080.d014182 m n θ p + _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1446.d019032 m n p)) := havg
      _ ≤ (2 : ℝ≥0∞)⁻¹ * (B θ + B θ) :=
        mul_le_mul_right (add_le_add (hpRisk θ) hrefl) _
      _ = B θ := by
        rw [← two_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hrraw : (r : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      qR ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    have hcomp := (_root_.GD.N0232.N0720.N1446.d019031 m n).quasiMeasurePreserving.ae_eq_comp
      hmem.coeFn_toLp
    filter_upwards [Lp.coeFn_smul (2 : ℝ)⁻¹ (p + _root_.GD.N0232.N0720.N1446.d019032 m n p),
      Lp.coeFn_add p (_root_.GD.N0232.N0720.N1446.d019032 m n p), _root_.GD.N0232.N0720.N1476.d019377 m n p,
      hmem.coeFn_toLp, hcomp] with x hsmul hadd hreflect hraw hrawNeg
    simp only [Function.comp_apply] at hrawNeg
    change p x = f x at hraw
    change p (_root_.GD.N0232.N0720.N1446.d019019 m n x) = f (_root_.GD.N0232.N0720.N1446.d019019 m n x) at hrawNeg
    change r x = qR (_root_.GD.N0232.N0720.N1467.d012542 m n x)
    dsimp only [r] at hsmul ⊢
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul, hadd, Pi.add_apply, hreflect]
    rw [hraw, hrawNeg]
    change (2 : ℝ)⁻¹ * (q (_root_.GD.N0232.N0720.N1467.d012542 m n x) -
      q (_root_.GD.N0232.N0720.N1467.d012542 m n (_root_.GD.N0232.N0720.N1446.d019019 m n x))) = _
    rw [_root_.GD.N0232.N0720.N1476.d019375 m n (by omega) (by omega)]
    dsimp only [qR, _root_.GD.N0232.N0720.N1476.d019361]
    ring
  have hqR : Measurable qR := _root_.GD.N0232.N0720.N1476.d019362 q hq
  have hqRb (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n θ
      (qR ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ≤ B θ := by
    have hae := (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le
      (hrraw.symm.trans (_root_.GD.N0232.N0720.N1214.d014267 m n r).symm)
    rw [_root_.GD.N0232.N0720.N1159.d014662 m n θ hae, _root_.GD.N0232.N0720.N1215.d014286]
    exact hrRisk θ
  let g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ := fun z => _root_.GD.N0232.N0720.N1209.d012471 qR z.1 z.2
  have hg : Measurable g := _root_.GD.N0232.N0720.N1209.d012473 qR hqR
  have hrep (θ : _root_.GD.N0232.N0720.N1080.d014168) : (qR ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
      _root_.GD.N0232.N0720.N1425.d014719 m n g :=
    _root_.GD.N0232.N0720.N1342.d019639 m n hm hn qR
      (_root_.GD.N0232.N0720.N1476.d019363 q hqaff)
      (_root_.GD.N0232.N0720.N1476.d019364 q) θ
  refine ⟨_root_.GD.N0232.N0720.N1286.d019582 g, _root_.GD.N0232.N0720.N1286.d019583 hg,
    _root_.GD.N0232.N0720.N1286.d019584 g, fun θ => ?_⟩
  have hgb : _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤ B θ := by
    rw [← _root_.GD.N0232.N0720.N1159.d014662 m n θ (hrep θ)]
    exact hqRb θ
  exact (_root_.GD.N0232.N0720.N1398.d019600 m n hm hn θ hg
    (ne_top_of_le_ne_top (hBfinite θ) hgb)).trans hgb

end
end GD.N0024.N0271

#print axioms _root_.GD.N0024.N0271.d028028
#print axioms _root_.GD.N0024.N0271.d028029
