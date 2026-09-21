import GD.Module1241
import GD.Module0892
import GD.Module1240











open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1303

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1337 _root_.GD.N0232.N0720.N1335
open _root_.GD.N0232.N0720.N1305 _root_.GD.N0232.N0720.N1307
open _root_.GD.N0232.N0720.N1306 _root_.GD.N0232.N0720.N1304
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1266 (d013726)
open _root_.GD.N0232.N0720.N1265
  (d020134 d020135 d020136 d020137)
open _root_.GD.N0230.N0622
open _root_.GD.N0230.N0556

noncomputable section

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
variable {I : Type*} [Fintype I]

theorem d020145 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1307.d013845 m n hm hn (_root_.GD.N0232.N0720.N1265.d020134 q) (_root_.GD.N0232.N0720.N1265.d020135 w) h =
      _root_.GD.N0232.N0720.N1337.d013826 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 h + ∑ i, w i * _root_.GD.N0232.N0720.N1337.d013826 m n hm hn (q i) h := by
  simp [_root_.GD.N0232.N0720.N1307.d013845, Fintype.sum_option, _root_.GD.N0232.N0720.N1265.d020134, _root_.GD.N0232.N0720.N1265.d020135]

theorem d020146 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 m n)
    (hbayes : _root_.GD.N0230.N0622.d000607 univ (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) _root_.GD.N0232.N0720.N1441.d013677 q w h) :
    h = _root_.GD.N0232.N0720.N1307.d013843 m n hm hn (_root_.GD.N0232.N0720.N1265.d020134 q) (_root_.GD.N0232.N0720.N1265.d020135 w)
      (_root_.GD.N0232.N0720.N1265.d020136 w hbayes.1) (_root_.GD.N0232.N0720.N1265.d020137 w) := by
  apply _root_.GD.N0232.N0720.N1307.d013852 m n hm hn
  intro k
  rw [_root_.GD.N0232.N0720.N1303.d020145 m n hm hn, _root_.GD.N0232.N0720.N1303.d020145 m n hm hn]
  exact hbayes.2 k (mem_univ k)

theorem d020147 : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
  (_root_.GD.N0232.N0720.N1436.d013290 m n (1 / 2)).ae_le
    (ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219)

theorem d020148
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (H : _root_.GD.N0232.N0720.N1441.d013681 m n)
    (hcenter : (H : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] _root_.GD.N0232.N0720.N1441.d013686 g)
    (hadm : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) H) :
    ∃ μ : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x)
        (μ j : Measure _root_.GD.N0232.N0720.N1290.d004131)) atTop (𝓝 (g x)) := by
  obtain ⟨sample, p, w, _hdense, hlim, hbayes⟩ :=
    _root_.GD.N0232.N0720.N1305.d020144 m n hm hn H hadm
  obtain ⟨ns, _hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  let q (j : ℕ) := _root_.GD.N0232.N0720.N1265.d020134 (fun i : Fin j ↦ sample i)
  let v (j : ℕ) := _root_.GD.N0232.N0720.N1265.d020135 (w j)
  have hv (j : ℕ) : ∀ i, 0 ≤ v j i := _root_.GD.N0232.N0720.N1265.d020136 (w j) (hbayes j).1
  have hvpos (j : ℕ) : ∃ i, 0 < v j i := _root_.GD.N0232.N0720.N1265.d020137 (w j)
  have heq (j : ℕ) : p j = _root_.GD.N0232.N0720.N1307.d013843 m n hm hn (q j) (v j) (hv j) (hvpos j) :=
    _root_.GD.N0232.N0720.N1303.d020146 m n hm hn _ _ _ (hbayes j)
  have hratio (j : ℕ) : p j =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦
      _root_.GD.N0232.N0720.N1307.d013838 m n hm hn (q j) (v j) (_root_.GD.N0232.N0720.N1266.d013726 x) /
        _root_.GD.N0232.N0720.N1307.d013837 m n hm hn (q j) (v j) (_root_.GD.N0232.N0720.N1266.d013726 x) := by
    rw [heq j]
    exact _root_.GD.N0232.N0720.N1307.d013844 m n hm hn (q j) (v j) (hv j) (hvpos j)
  let μ (j : ℕ) := _root_.GD.N0232.N0720.N1306.d013858 m n (q (ns j)) (v (ns j))
  refine ⟨μ, ?_⟩
  have hratios : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, ∀ j,
      p j x = _root_.GD.N0232.N0720.N1307.d013838 m n hm hn (q j) (v j) (_root_.GD.N0232.N0720.N1266.d013726 x) /
        _root_.GD.N0232.N0720.N1307.d013837 m n hm hn (q j) (v j) (_root_.GD.N0232.N0720.N1266.d013726 x) := ae_all_iff.mpr hratio
  filter_upwards [hpoint, hratios, _root_.GD.N0232.N0720.N1303.d020147 m n, hcenter]
    with x hx hrat hphys hraw
  have hident (j : ℕ) : _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x)
      (μ j : Measure _root_.GD.N0232.N0720.N1290.d004131) = p (ns j) x + 1 / 2 := by
    rw [hrat (ns j)]
    exact (_root_.GD.N0232.N0720.N1306.d013865 m n hm hn (q (ns j)) (v (ns j))
      (hv (ns j)) (hvpos (ns j)) hphys).symm
  have hshift := hx.add_const (1 / 2 : ℝ)
  simpa only [hident, hraw, _root_.GD.N0232.N0720.N1441.d013686, sub_add_cancel] using hshift

include hm hn in


theorem d020149
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    ∃ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131),
      Measurable g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1425.d014719 m n g
          =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d) ∧
      (g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦
        _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) (μ : Measure _root_.GD.N0232.N0720.N1290.d004131)) := by
  obtain ⟨g, H, hg, hb, hcenter, hadm, hrep⟩ :=
    _root_.GD.N0232.N0720.N1335.d020092 m n hm hn hd
  obtain ⟨μ, hμ⟩ := _root_.GD.N0232.N0720.N1303.d020148 m n hm hn g H hcenter hadm
  have hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      Continuous (_root_.GD.N0232.N0720.N1336.d013420 m n x) ∧ ∀ t, 0 < _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
    filter_upwards [_root_.GD.N0232.N0720.N1303.d020147 m n] with x hx
    exact ⟨(_root_.GD.N0232.N0720.N1336.d013421 m n).comp (continuous_const.prodMk continuous_id),
      _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx⟩
  obtain ⟨ν, hν⟩ := _root_.GD.N0232.N0720.N1304.d004178 (_root_.GD.N0232.N0720.N1441.d013679 m n)
    (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n) g μ hP hμ
  exact ⟨g, ν, hg, hb, hrep, hν⟩

end
end GD.N0232.N0720.N1303

#print axioms _root_.GD.N0232.N0720.N1303.d020146
#print axioms _root_.GD.N0232.N0720.N1303.d020148
#print axioms _root_.GD.N0232.N0720.N1303.d020149
