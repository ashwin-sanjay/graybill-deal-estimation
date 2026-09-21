import GD.Module1239
import GD.Module0888
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
















open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1265

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1400
open _root_.GD.N0232.N0720.N1266 _root_.GD.N0232.N0720.N1272
open _root_.GD.N0232.N0720.N1267 _root_.GD.N0232.N0720.N1268
open _root_.GD.N0232.N0720.N1269 _root_.GD.N0232.N0720.N1291
open _root_.GD.N0232.N0720.N1271 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0230.N0622

variable {I : Type*} [Fintype I]

def d020134 (q : I → _root_.GD.N0232.N0720.N1441.d013676) : Option I → _root_.GD.N0232.N0720.N1441.d013676
  | none => _root_.GD.N0232.N0720.N1441.d013677
  | some i => q i

def d020135 (w : I → ℝ) : Option I → ℝ
  | none => 1
  | some i => w i

omit [Fintype I] in
theorem d020136 (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1265.d020135 w i := by
  intro i
  cases i with
  | none => exact zero_le_one
  | some i => exact hw i

omit [Fintype I] in
theorem d020137 (w : I → ℝ) : ∃ i, 0 < _root_.GD.N0232.N0720.N1265.d020135 w i :=
  ⟨none, zero_lt_one⟩

theorem d020138 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1268.d013772 (_root_.GD.N0232.N0720.N1265.d020134 q) (_root_.GD.N0232.N0720.N1265.d020135 w) h =
      _root_.GD.N0232.N0720.N1272.d013752 _root_.GD.N0232.N0720.N1441.d013677 h + ∑ i, w i * _root_.GD.N0232.N0720.N1272.d013752 (q i) h := by
  simp [_root_.GD.N0232.N0720.N1268.d013772, Fintype.sum_option, _root_.GD.N0232.N0720.N1265.d020134, _root_.GD.N0232.N0720.N1265.d020135]

theorem d020139 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 2 2)
    (hbayes : _root_.GD.N0230.N0622.d000607 univ _root_.GD.N0232.N0720.N1272.d013752 _root_.GD.N0232.N0720.N1441.d013677 q w h) :
    h = _root_.GD.N0232.N0720.N1268.d013770 (_root_.GD.N0232.N0720.N1265.d020134 q) (_root_.GD.N0232.N0720.N1265.d020135 w)
      (_root_.GD.N0232.N0720.N1265.d020136 w hbayes.1) (_root_.GD.N0232.N0720.N1265.d020137 w) := by
  apply _root_.GD.N0232.N0720.N1268.d013779
  intro k
  rw [_root_.GD.N0232.N0720.N1265.d020138, _root_.GD.N0232.N0720.N1265.d020138]
  exact hbayes.2 k (mem_univ k)

theorem d020140 : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
  (_root_.GD.N0232.N0720.N1436.d013290 2 2 (1 / 2)).ae_le
    (ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219)



theorem d020141 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ mu : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1291.d013416 (mu n) x) atTop (𝓝 (_root_.GD.N0232.N0720.N1398.d019601 d x)) := by
  obtain ⟨sample, p, w, _hdense, hlim, hbayes⟩ := _root_.GD.N0232.N0720.N1267.d020133 hd
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  let q (n : ℕ) := _root_.GD.N0232.N0720.N1265.d020134 (fun i : Fin n ↦ sample i)
  let v (n : ℕ) := _root_.GD.N0232.N0720.N1265.d020135 (w n)
  have hv (n : ℕ) : ∀ i, 0 ≤ v n i := _root_.GD.N0232.N0720.N1265.d020136 (w n) (hbayes n).1
  have hvpos (n : ℕ) : ∃ i, 0 < v n i := _root_.GD.N0232.N0720.N1265.d020137 (w n)
  have heq (n : ℕ) : p n = _root_.GD.N0232.N0720.N1268.d013770 (q n) (v n) (hv n) (hvpos n) :=
    _root_.GD.N0232.N0720.N1265.d020139 _ _ _ (hbayes n)
  have hratio (n : ℕ) : p n =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦
      _root_.GD.N0232.N0720.N1268.d013765 (q n) (v n) (_root_.GD.N0232.N0720.N1266.d013726 x) / _root_.GD.N0232.N0720.N1268.d013764 (q n) (v n) (_root_.GD.N0232.N0720.N1266.d013726 x) := by
    rw [heq n]
    exact _root_.GD.N0232.N0720.N1268.d013771 (q n) (v n) (hv n) (hvpos n)
  let mu (n : ℕ) := _root_.GD.N0232.N0720.N1269.d013785 (q (ns n)) (v (ns n))
  refine ⟨mu, ?_⟩
  have hratios : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, ∀ n,
      p n x = _root_.GD.N0232.N0720.N1268.d013765 (q n) (v n) (_root_.GD.N0232.N0720.N1266.d013726 x) /
        _root_.GD.N0232.N0720.N1268.d013764 (q n) (v n) (_root_.GD.N0232.N0720.N1266.d013726 x) := ae_all_iff.mpr hratio
  filter_upwards [hpoint, hratios, _root_.GD.N0232.N0720.N1265.d020140,
    _root_.GD.N0232.N0720.N1400.d020125 hd] with x hx hrat hphys hraw
  have hident (n : ℕ) : _root_.GD.N0232.N0720.N1291.d013416 (mu n) x = p (ns n) x + 1 / 2 := by
    rw [hrat (ns n)]
    exact (_root_.GD.N0232.N0720.N1269.d013792 (q (ns n)) (v (ns n))
      (hv (ns n)) (hvpos (ns n)) hphys).symm
  have hshift := hx.add_const (1 / 2 : ℝ)
  simpa only [hident, hraw, _root_.GD.N0232.N0720.N1441.d013686, sub_add_cancel] using hshift




theorem d020142 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ mu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131,
      _root_.GD.N0232.N0720.N1398.d019601 d =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦
        _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  obtain ⟨mu, hmu⟩ := _root_.GD.N0232.N0720.N1265.d020141 hd
  exact _root_.GD.N0232.N0720.N1291.d013419 mu (_root_.GD.N0232.N0720.N1398.d019601 d)
    (_root_.GD.N0232.N0720.N1441.d013679 2 2) _root_.GD.N0232.N0720.N1265.d020140 hmu

end
end GD.N0232.N0720.N1265

#print axioms _root_.GD.N0232.N0720.N1265.d020139
#print axioms _root_.GD.N0232.N0720.N1265.d020141
#print axioms _root_.GD.N0232.N0720.N1265.d020142
