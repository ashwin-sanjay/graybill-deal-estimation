import GD.Module1263
import GD.Module0825
import GD.Module1221

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0460

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0976 _root_.GD.N0232.N0719.N0975
open _root_.GD.N0213.N0477
open _root_.GD.N0232.N0720.N1341

noncomputable section
variable {k d : ℕ} [NeZero k]
variable (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)
variable {J : Type*} [Fintype J]



theorem d020403
    (a : J → _root_.GD.N0213.N0477.d020377 k) (w : J → ℝ)
    (hn : ∀ i, 0 < sizes i) (hw : ∀ j, 0 ≤ w j) (hwpos : ∃ j, 0 < w j)
    (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0232.N0719.N0975.d019765 (fun j => _root_.GD.N0213.N0477.d020380 sizes hdim (a j)) w u /
      _root_.GD.N0232.N0719.N0975.d019764 (fun j => _root_.GD.N0213.N0477.d020380 sizes hdim (a j)) w u =
    _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
      (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
      (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
      (_root_.GD.N0213.N0477.d020400 sizes hdim a w : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  exact _root_.GD.N0213.N0477.d020401 sizes hdim a w hn hw hwpos u

omit [Fintype J] in


theorem d020404
    {Index : ℕ → Type*} [∀ j, Fintype (Index j)]
    (a : ∀ j, Index j → _root_.GD.N0213.N0477.d020377 k) (w : ∀ j, Index j → ℝ)
    (hn : ∀ i, 0 < sizes i) (hw : ∀ j i, 0 ≤ w j i) (hwpos : ∀ j, ∃ i, 0 < w j i)
    (g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ)
    (hr : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes
      (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) i)
    (hlim : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      Tendsto (fun j => _root_.GD.N0232.N0719.N0975.d019765
        (fun i => _root_.GD.N0213.N0477.d020380 sizes hdim (a j i)) (w j) u /
        _root_.GD.N0232.N0719.N0975.d019764 (fun i => _root_.GD.N0213.N0477.d020380 sizes hdim (a j i)) (w j) u)
        atTop (𝓝 (g u))) :
    ∃ π : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      g =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] fun u => _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
        (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
        (π : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  exact _root_.GD.N0213.N0477.d020402 sizes hdim a w hn hw hwpos g hr hlim

section Family
variable {Θ : Type*} [TopologicalSpace Θ] [SecondCountableTopology Θ]

omit [Fintype J] in



theorem d020405
    (A : Θ → _root_.GD.N0213.N0477.d020377 k)
    (hA : Continuous (fun θ => _root_.GD.N0213.N0477.d020380 sizes hdim (A θ))) (ref : Θ)
    (hn : ∀ i, 0 < sizes i) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hadmissible : _root_.GD.N0230.N0556.d000031
      (_root_.GD.N0232.N0719.N0975.d019769 (fun θ => _root_.GD.N0213.N0477.d020380 sizes hdim (A θ)) ref) h)
    (hr : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes
      (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) i) :
    ∃ π : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      (fun u => _root_.GD.N0232.N0719.N0976.d019748 (_root_.GD.N0213.N0477.d020380 sizes hdim (A ref)) u (h u))
        =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] fun u => _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
          (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (π : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  let tau : Θ → _root_.GD.N0232.N0719.N0976.d019733 d := fun θ => _root_.GD.N0213.N0477.d020380 sizes hdim (A θ)
  obtain ⟨w, ns, hw, _hns, hlim⟩ :=
    _root_.GD.N0232.N0719.N0975.d019776 tau hA ref h hadmissible
  let atoms (j : ℕ) : Option (Fin (ns j)) → _root_.GD.N0213.N0477.d020377 k
    | none => A ref
    | some i => A (_root_.GD.N0232.N0719.N0975.d019770 ref i)
  let weights (j : ℕ) : Option (Fin (ns j)) → ℝ :=
    _root_.GD.N0232.N0720.N1314.d019720 (w (ns j))
  apply _root_.GD.N0212.N0460.d020404 sizes hdim atoms weights hn
    (fun j => _root_.GD.N0232.N0720.N1314.d019721
      (w (ns j)) (hw (ns j)))
    (fun j => _root_.GD.N0232.N0720.N1314.d019722
      (w (ns j))) _ hr
  have hatoms (j : ℕ) : (fun i => _root_.GD.N0213.N0477.d020380 sizes hdim (atoms j i)) =
      _root_.GD.N0232.N0719.N0975.d019772 tau ref (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0975.d019770 ref i) := by
    funext i
    cases i <;> rfl
  simpa only [hatoms] using hlim

end Family

end
end GD.N0212.N0460

#print axioms _root_.GD.N0212.N0460.d020403
#print axioms _root_.GD.N0212.N0460.d020404

#print axioms _root_.GD.N0212.N0460.d020405
