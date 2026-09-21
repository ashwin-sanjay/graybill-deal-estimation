import GD.Module1898
import GD.Module0560
import GD.Module0558
import GD.Module1901

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0010
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1089
open _root_.GD.N0230.N0611
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0335
open _root_.GD.N0082.N0336
open _root_.GD.N0149.N0432 _root_.GD.N0149.N0433
open _root_.GD.N0011



theorem d030849 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ ENNReal.ofReal C) :
    1 + Real.pi / 4 ≤ C := by
  have hi := (_root_.GD.N0011.d030819 H hHm hHI C hC).mp hcap
  have hb : _root_.GD.N0149.N0433.d008323 H :=
    _root_.GD.N0006.d008332 H hHm (C - 1)
      (fun _ ht => _root_.GD.N0149.N0436.d030845
        H hHm (fun u _ => hHI u) ht)
      (fun t ht => by have := hi t ht; linarith)
  exact _root_.GD.N0011.d030820 H hb hHI C hC hcap

theorem d030850 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (1 + Real.pi / 4) ≤ _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) := by
  by_cases ht : _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) = ⊤
  · rw [ht]
    exact le_top
  let C := (_root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H)).toReal
  have hc : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) :=
    ENNReal.ofReal_toReal ht
  have hcap (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
      ENNReal.ofReal C := by
    rw [hc]
    exact le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H)) θ
  rw [← hc]
  exact ENNReal.ofReal_le_ofReal
    (_root_.GD.N0010.d030849 H hHm hHI C ENNReal.toReal_nonneg hcap)

theorem d030851 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 θ _root_.GD.N0149.N0432.d030808 ≤ ENNReal.ofReal (1 + Real.pi / 4) := by
  rw [_root_.GD.N0149.N0432.d030808, _root_.GD.N0011.d030818 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282
    _root_.GD.N0149.N0432.d008281]
  apply ENNReal.ofReal_le_ofReal
  have h := _root_.GD.N0016.d008321
    (_root_.GD.N0082.N0336.d030741 θ) ⟨(_root_.GD.N0082.N0336.d030742 θ).1.le, (_root_.GD.N0082.N0336.d030742 θ).2.le⟩
  linarith

theorem d030852 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 θ _root_.GD.N0149.N0432.d030808 < ENNReal.ofReal (1 + Real.pi / 4) := by
  rw [_root_.GD.N0149.N0432.d030808, _root_.GD.N0011.d030818 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282
    _root_.GD.N0149.N0432.d008281]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  have h := _root_.GD.N0016.d008320
    (_root_.GD.N0082.N0336.d030741 θ) (_root_.GD.N0082.N0336.d030742 θ)
  linarith



theorem d030853 :
    _root_.GD.N0232.N0720.N1256.d015548 3 3 _root_.GD.N0149.N0432.d030808 = ENNReal.ofReal (1 + Real.pi / 4) :=
  le_antisymm (iSup_le _root_.GD.N0010.d030851)
    (_root_.GD.N0010.d030850 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282 _root_.GD.N0149.N0432.d008281)



theorem d030854 :
    IsLeast ((fun H : ℝ → ℝ => _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H)) ''
      {H | Measurable H ∧ ∀ u, H u ∈ Icc (0 : ℝ) 1})
      (ENNReal.ofReal (1 + Real.pi / 4)) := by
  constructor
  · exact ⟨_root_.GD.N0232.N0720.N1089.d003092, ⟨_root_.GD.N0149.N0432.d008282, _root_.GD.N0149.N0432.d008281⟩,
      _root_.GD.N0010.d030853⟩
  · rintro x ⟨H, ⟨hHm, hHI⟩, rfl⟩
    exact _root_.GD.N0010.d030850 H hHm hHI

theorem d030855 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 ≤ ENNReal.ofReal (1 + Real.pi / 4) := by
  have h : _root_.GD.N0232.N0720.N1256.d015549 3 3 ≤ _root_.GD.N0232.N0720.N1256.d015548 3 3 _root_.GD.N0149.N0432.d030808 :=
    _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 3 3) _root_.GD.N0149.N0432.d030809.1
  exact h.trans _root_.GD.N0010.d030853.le

theorem d030856 : _root_.GD.N0232.N0720.N1256.d015549 3 3 < 2 := by
  apply _root_.GD.N0010.d030855.trans_lt
  have h : ENNReal.ofReal (1 + Real.pi / 4) < ENNReal.ofReal 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith [Real.pi_lt_four])
  simpa using h


theorem d030857 :
    (1 + Real.pi / 4 : ℝ) < 25 / 14 := by
  linarith [Real.pi_lt_d4]

theorem d030858 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 < ENNReal.ofReal (25 / 14) :=
  _root_.GD.N0010.d030855.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
      _root_.GD.N0010.d030857)



theorem d030859 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1)
    (hdom : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
      _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ ENNReal.ofReal C) :
    2 ≤ C := by
  have hae := (_root_.GD.N0149.N0436.d030847
    H hHm hHI hdom).1
  have he0 : _root_.GD.N0082.N0334.d008258 H 0 = 1 := by
    calc
      _ = _root_.GD.N0082.N0334.d008258 id 0 := by
        unfold _root_.GD.N0082.N0334.d008258
        apply integral_congr_ae
        filter_upwards [hae] with u hu
        rw [hu]
      _ = 1 := _root_.GD.N0082.N0334.d008273
  have hi := (_root_.GD.N0011.d030819 H hHm hHI C hC).mp hcap
  have hb := (_root_.GD.N0006.d008333
    H hHm (C - 1)
      (fun _ ht => _root_.GD.N0149.N0436.d030845
        H hHm (fun u _ => hHI u) ht)
      (fun t ht => by have := hi t ht; linarith)).1
  rw [he0] at hb
  linarith



theorem d030860 :
    ¬ ∃ H : ℝ → ℝ, Measurable H ∧ (∀ u, H u ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
        _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ) ∧
      _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ _root_.GD.N0232.N0720.N1256.d015549 3 3 := by
  rintro ⟨H, hHm, hHI, hdom, hmin⟩
  have hcap (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
      ENNReal.ofReal (1 + Real.pi / 4) :=
    (le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H)) θ).trans
      (hmin.trans _root_.GD.N0010.d030855)
  have h := _root_.GD.N0010.d030859 H hHm hHI hdom
    (1 + Real.pi / 4) (by positivity) hcap
  linarith [Real.pi_lt_four]

end
end GD.N0010

#print axioms _root_.GD.N0010.d030849
#print axioms _root_.GD.N0010.d030850
#print axioms _root_.GD.N0010.d030851
#print axioms _root_.GD.N0010.d030852
#print axioms _root_.GD.N0010.d030853
#print axioms _root_.GD.N0010.d030854
#print axioms _root_.GD.N0010.d030855
#print axioms _root_.GD.N0010.d030856
#print axioms _root_.GD.N0010.d030857
#print axioms _root_.GD.N0010.d030858
#print axioms _root_.GD.N0010.d030859
#print axioms _root_.GD.N0010.d030860
