import GD.Module1744
import GD.Module1841

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0034.N0295

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0608
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0286

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030302 {ι : Type*} (F : Finset ι)
    (w a b : ι → ℝ) (hw : ∀ i ∈ F, 0 ≤ w i) :
    (∑ i ∈ F, w i * min (a i) (b i)) ≤
      min (∑ i ∈ F, w i * a i) (∑ i ∈ F, w i * b i) := by
  apply le_min
  · exact Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (min_le_left _ _) (hw i hi))
  · exact Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (min_le_right _ _) (hw i hi))

theorem d030303 : _root_.GD.N0034.N0299.d030297 m n hm hn :=
  _root_.GD.N0034.N0300.d028979 m n hm hn

theorem d030304 :
    _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ :=
  _root_.GD.N0034.N0299.d030298 m n hm hn (_root_.GD.N0034.N0295.d030303 m n hm hn)

theorem d030305 :
    _root_.GD.N0034.N0286.d030283 m n hm hn ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty :=
  _root_.GD.N0034.N0299.d030299 m n hm hn
    (_root_.GD.N0034.N0295.d030303 m n hm hn)

theorem d030306 :
    _root_.GD.N0034.N0286.d030283 m n hm hn ↔ _root_.GD.N0034.N0289.d030224 m n hm hn :=
  _root_.GD.N0034.N0299.d030300 m n hm hn
    (_root_.GD.N0034.N0295.d030303 m n hm hn)

theorem d030307 :
    ¬ _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0034.N0289.d030224 m n hm hn :=
  (_root_.GD.N0034.N0286.d030284 m n hm hn).trans (_root_.GD.N0034.N0295.d030306 m n hm hn)

theorem d030308 (p : _root_.GD.N0046.N0305.d030201 m n) : _root_.GD.N0046.N0305.d030202 m n hm hn ≠ {p} :=
  _root_.GD.N0034.N0299.d030301 m n hm hn
    (_root_.GD.N0034.N0295.d030303 m n hm hn) p

theorem d030309 :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔ _root_.GD.N0232.N0720.N1226.d015578 m n :=
  (_root_.GD.N0034.N0295.d030305 m n hm hn).symm.trans
    (_root_.GD.N0034.N0286.d030286 m n hm hn)

theorem d030310
    (p : _root_.GD.N0046.N0305.d030201 m n) (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    ∃ t ∈ _root_.GD.N0046.N0305.d030202 m n hm hn,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ t ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ p) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) t ∧ 0 < _root_.GD.N0034.N0287.d021571 m n t := by
  let t := _root_.GD.N0232.N0720.N1159.d014633 m n p
  have hbelow := (_root_.GD.N0232.N0720.N1159.d014634 m n p).1
  have ht : t ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
    intro θ
    exact ⟨(hbelow θ).trans (hp θ).1, (hbelow θ).trans (hp θ).2⟩
  have htfin := _root_.GD.N0046.N0305.d030204 m n ht
  have hterm : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) t :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n p).2.1
  refine ⟨t, ht, hbelow, hterm, ?_⟩
  apply lt_of_le_of_ne (_root_.GD.N0034.N0287.d021575 m n t)
  intro hz
  have hfixed := (_root_.GD.N0034.N0287.d021580 m n t htfin).mp hz.symm
  have hrep := (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn t htfin).mp hfixed
  exact _root_.GD.N0034.N0295.d030303 m n hm hn t htfin hrep (fun θ => (ht θ).2) hterm

theorem d030311 :
    (¬ _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0034.N0286.d030283 m n hm hn) ∧
    (_root_.GD.N0034.N0286.d030283 m n hm hn ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) ∧
    (_root_.GD.N0034.N0286.d030283 m n hm hn ↔ _root_.GD.N0034.N0289.d030224 m n hm hn) ∧
    (_root_.GD.N0034.N0286.d030283 m n hm hn ↔ _root_.GD.N0232.N0720.N1226.d015578 m n) ∧
    (_root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0046.N0305.d030202 m n hm hn = ∅) :=
  ⟨_root_.GD.N0034.N0286.d030284 m n hm hn,
    _root_.GD.N0034.N0295.d030305 m n hm hn,
    _root_.GD.N0034.N0295.d030306 m n hm hn,
    _root_.GD.N0034.N0286.d030286 m n hm hn,
    _root_.GD.N0034.N0295.d030304 m n hm hn⟩

end
end GD.N0034.N0295

#print axioms _root_.GD.N0034.N0295.d030303
#print axioms _root_.GD.N0034.N0295.d030304
#print axioms _root_.GD.N0034.N0295.d030305
#print axioms _root_.GD.N0034.N0295.d030306
#print axioms _root_.GD.N0034.N0295.d030307
#print axioms _root_.GD.N0034.N0295.d030308
#print axioms _root_.GD.N0034.N0295.d030309
#print axioms _root_.GD.N0034.N0295.d030310
#print axioms _root_.GD.N0034.N0295.d030311
#print axioms _root_.GD.N0034.N0295.d030302
