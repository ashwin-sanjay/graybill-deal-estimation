import GD.Module1834
import GD.Module1514
import GD.Module1517
import GD.Module1847
import GD.Module1279

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0024.N0268

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0289
open _root_.GD.N0024.N0275

theorem d030374 :
    _root_.GD.N0046.N0305.d030202 6 6 (by norm_num) (by norm_num) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hK
  let v : ℝ := (_root_.GD.N0232.N0720.N1256.d015549 6 6).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hvalue : _root_.GD.N0232.N0720.N1256.d015549 6 6 = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal _root_.GD.N0024.N0279.d023585).symm
  obtain ⟨g, hg, hb, hbound⟩ :=
    _root_.GD.N0024.N0270.d030252
      6 6 (by norm_num) (by norm_num) v hv hvalue hK
  have hcap := _root_.GD.N0024.N0275.d022900 g hg hb v hv (fun θ => (hbound θ).1)
  have hbase := _root_.GD.N0024.N0279.d023586
    g hg hb (fun θ => (hbound θ).2)
  have hn : 0 ≤ _root_.GD.N0024.N0277.d007882 (_root_.GD.N0232.N0720.N1441.d013678 6 6) g
      _root_.GD.N0024.N0276.d007902 :=
    div_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (_root_.GD.N0024.N0277.d007880 _root_.GD.N0024.N0276.d007902).le
  have hvpos : 0 < v := by linarith [hcap _root_.GD.N0024.N0276.d007902]
  exact _root_.GD.N0024.N0282.d023609 g hg hb (v - 1) hcap hbase
    (_root_.GD.N0024.N0275.d022901 v hvalue hvpos)

theorem d030375 : _root_.GD.N0024.N0283.d030364 6 6 = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rw [_root_.GD.N0024.N0283.d030366 6 6 (by norm_num) (by norm_num),
    _root_.GD.N0024.N0268.d030374]
  simp

theorem d030376 :
    ∀ f : _root_.GD.N0232.N0720.N1080.d014170 6 6 → ℝ, Measurable f →
      ∃ θ : _root_.GD.N0232.N0720.N1080.d014168,
        min (_root_.GD.N0232.N0720.N1080.d014197 6 6 θ (_root_.GD.N0024.N0283.d030361 6 6))
          (_root_.GD.N0232.N0720.N1256.d015549 6 6 * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 6 6 θ)) <
            _root_.GD.N0232.N0720.N1080.d014197 6 6 θ f := by
  intro f hf
  by_contra hnot
  push Not at hnot
  have hmem : f ∈ _root_.GD.N0024.N0283.d030364 6 6 := ⟨hf, hnot⟩
  rw [_root_.GD.N0024.N0268.d030375] at hmem
  exact hmem

theorem d030377 : ¬ _root_.GD.N0024.N0283.d030369 :=
  _root_.GD.N0024.N0283.d030373
    ⟨(6, 6), by constructor <;> norm_num⟩ _root_.GD.N0024.N0268.d030375

theorem d030378 :
    ¬ ∃ f : (i : _root_.GD.N0024.N0283.d030368) → _root_.GD.N0232.N0720.N1080.d014170 i.val.1 i.val.2 → ℝ,
      ∀ i, Measurable (f i) ∧ ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 i.val.1 i.val.2 θ (f i) ≤
          min (_root_.GD.N0232.N0720.N1080.d014197 i.val.1 i.val.2 θ
            (_root_.GD.N0024.N0283.d030361 i.val.1 i.val.2))
            (_root_.GD.N0232.N0720.N1220.d017310 i.val.1 i.val.2 *
              ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 i.val.1 i.val.2 θ)) := by
  rintro ⟨f, hf⟩
  apply _root_.GD.N0024.N0268.d030377
  refine ⟨f, fun i => ⟨(hf i).1, fun θ => ?_⟩⟩
  rw [_root_.GD.N0232.N0720.N1220.d017311 _ _ i.property.1 i.property.2]
  exact (hf i).2 θ

theorem d030379 :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) ∧
      _root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1080.d014169 +
        ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num) θ <
          _root_.GD.N0232.N0720.N1220.d017301 6 6 F w :=
  (_root_.GD.N0034.N0289.d030226 6 6 (by norm_num) (by norm_num)).mp
    _root_.GD.N0024.N0268.d030374

theorem d030380 :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) ∧
      _root_.GD.N0024.N0274.d030346 6 6 (_root_.GD.N0232.N0720.N1256.d015549 6 6).toReal F w <
        _root_.GD.N0024.N0274.d030345 6 6 (by norm_num) (by norm_num)
          (_root_.GD.N0232.N0720.N1256.d015549 6 6).toReal F w := by
  obtain ⟨F, w, hw, hgap⟩ := _root_.GD.N0024.N0268.d030379
  refine ⟨F, w, hw, ?_⟩
  have hid := _root_.GD.N0024.N0274.d030349 6 6 (by norm_num) (by norm_num)
    (_root_.GD.N0232.N0720.N1256.d015549 6 6).toReal ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal _root_.GD.N0024.N0279.d023585).symm F w
  change _ - (_root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1080.d014169 +
    ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num) θ) = _ at hid
  linarith

theorem d030381 : (_root_.GD.N0024.N0283.d030364 2 2).Nonempty :=
  _root_.GD.N0024.N0283.d030367 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0024.N0263.d020636

theorem d030382 :
    ¬ ∃ f : _root_.GD.N0232.N0720.N1080.d014170 6 6 → ℝ, _root_.GD.N0232.N0720.N1226.d015576 6 6 f := by
  rintro ⟨f, hf, hstrict, heq⟩
  have hfinite := _root_.GD.N0024.N0279.d023585
  let v := (_root_.GD.N0232.N0720.N1256.d015549 6 6).toReal
  have hvalue : _root_.GD.N0232.N0720.N1256.d015549 6 6 = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal hfinite).symm
  have hmem : f ∈ _root_.GD.N0034.N0294.d030312 6 6 := by
    refine ⟨hf, fun θ => ⟨?_, (hstrict θ).le⟩⟩
    have hnorm : _root_.GD.N0232.N0720.N1256.d015547 6 6 θ f ≤ ENNReal.ofReal v := by
      rw [← hvalue, ← heq]
      exact le_iSup (_root_.GD.N0232.N0720.N1256.d015547 6 6 · f) θ
    have hr := (_root_.GD.N0232.N0720.N1256.d015553 6 6 (by norm_num) v
      ENNReal.toReal_nonneg θ f).mp hnorm
    rwa [hvalue, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [← _root_.GD.N0024.N0283.d030365 6 6 (by norm_num) (by norm_num),
    _root_.GD.N0024.N0268.d030375] at hmem
  exact hmem

theorem d030383 : ¬ _root_.GD.N0232.N0720.N1226.d015578 6 6 := by
  rintro ⟨f, hf, _⟩
  exact _root_.GD.N0024.N0268.d030382 ⟨f, hf⟩

theorem d030384 :
    ¬ _root_.GD.N0024.N0283.d030369 ∧
    _root_.GD.N0024.N0283.d030364 6 6 = ∅ ∧
    (_root_.GD.N0024.N0283.d030364 2 2).Nonempty ∧
    _root_.GD.N0232.N0720.N1256.d015549 6 6 ≤ ENNReal.ofReal (289 / 3) ∧
    _root_.GD.N0232.N0720.N1256.d015549 2 2 = ⊤ ∧
    ¬ _root_.GD.N0232.N0720.N1226.d015578 6 6 :=
  ⟨_root_.GD.N0024.N0268.d030377, _root_.GD.N0024.N0268.d030375, _root_.GD.N0024.N0268.d030381,
    _root_.GD.N0024.N0279.d023584,
    _root_.GD.N0024.N0263.d020636, _root_.GD.N0024.N0268.d030383⟩

end
end GD.N0024.N0268

#print axioms _root_.GD.N0024.N0268.d030374
#print axioms _root_.GD.N0024.N0268.d030375
#print axioms _root_.GD.N0024.N0268.d030376
#print axioms _root_.GD.N0024.N0268.d030377
#print axioms _root_.GD.N0024.N0268.d030378
#print axioms _root_.GD.N0024.N0268.d030379
#print axioms _root_.GD.N0024.N0268.d030380
#print axioms _root_.GD.N0024.N0268.d030381
#print axioms _root_.GD.N0024.N0268.d030382
#print axioms _root_.GD.N0024.N0268.d030383
#print axioms _root_.GD.N0024.N0268.d030384
