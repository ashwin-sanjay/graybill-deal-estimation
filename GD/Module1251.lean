import GD.Module1250
import Mathlib.Analysis.Calculus.Deriv.Shift















open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1368

open _root_.GD.N0232.N0720.N1290 _root_.GD.N0232.N0720.N1414
open _root_.GD.N0232.N0720.N1402 _root_.GD.N0232.N0720.N1271
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1441

noncomputable section

def d020208 (z w u : ℝ) (t : _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  z * (1 - (t : ℝ)) + w * (t : ℝ) + u * (t : ℝ) * (1 - (t : ℝ))

def d020209 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1368.d020208 z w u) mu

def d020210 (g : ℝ → ℝ → ℝ → ℝ) (z w u : ℝ) : ℝ :=
  g z w u ^ 2 * deriv (fun v ↦ g v w u) z +
    (1 - g z w u) ^ 2 * deriv (fun v ↦ g z v u) w -
      deriv (fun v ↦ g z w v) u

theorem d020211 (q : ℝ) (P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (v : ℝ) :
    _root_.GD.N0232.N0720.N1290.d004137 q P H mu v = _root_.GD.N0232.N0720.N1290.d004140 q (fun t ↦ P t + v * H t) mu := by
  simp only [_root_.GD.N0232.N0720.N1290.d004137, _root_.GD.N0232.N0720.N1290.d004132, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139, one_mul]

theorem d020212 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu (z + v) w u) =
      _root_.GD.N0232.N0720.N1290.d004137 q (_root_.GD.N0232.N0720.N1368.d020208 z w u) (fun t ↦ 1 - (t : ℝ)) mu := by
  funext v
  rw [_root_.GD.N0232.N0720.N1368.d020211]
  unfold _root_.GD.N0232.N0720.N1368.d020209
  congr 1
  funext t
  unfold _root_.GD.N0232.N0720.N1368.d020208
  ring

theorem d020213 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z (w + v) u) =
      _root_.GD.N0232.N0720.N1290.d004137 q (_root_.GD.N0232.N0720.N1368.d020208 z w u) (fun t ↦ (t : ℝ)) mu := by
  funext v
  rw [_root_.GD.N0232.N0720.N1368.d020211]
  unfold _root_.GD.N0232.N0720.N1368.d020209
  congr 1
  funext t
  unfold _root_.GD.N0232.N0720.N1368.d020208
  ring

theorem d020214 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z w (u + v)) =
      _root_.GD.N0232.N0720.N1290.d004137 q (_root_.GD.N0232.N0720.N1368.d020208 z w u) (fun t ↦ (t : ℝ) * (1 - (t : ℝ))) mu := by
  funext v
  rw [_root_.GD.N0232.N0720.N1368.d020211]
  unfold _root_.GD.N0232.N0720.N1368.d020209
  congr 1
  funext t
  unfold _root_.GD.N0232.N0720.N1368.d020208
  ring

theorem d020215 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    deriv (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu v w u) z =
      deriv (_root_.GD.N0232.N0720.N1290.d004137 q (_root_.GD.N0232.N0720.N1368.d020208 z w u) (fun t ↦ 1 - (t : ℝ)) mu) 0 := by
  calc
    _ = deriv (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu (z + v) w u) 0 := by
      simpa only [add_zero] using
        (deriv_comp_const_add (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu v w u) z 0).symm
    _ = _ := congrArg (fun f : ℝ → ℝ ↦ deriv f 0) (_root_.GD.N0232.N0720.N1368.d020212 q mu z w u)

theorem d020216 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    deriv (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z v u) w =
      deriv (_root_.GD.N0232.N0720.N1290.d004137 q (_root_.GD.N0232.N0720.N1368.d020208 z w u) (fun t ↦ (t : ℝ)) mu) 0 := by
  calc
    _ = deriv (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z (w + v) u) 0 := by
      simpa only [add_zero] using
        (deriv_comp_const_add (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z v u) w 0).symm
    _ = _ := congrArg (fun f : ℝ → ℝ ↦ deriv f 0) (_root_.GD.N0232.N0720.N1368.d020213 q mu z w u)

theorem d020217 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    deriv (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z w v) u =
      deriv (_root_.GD.N0232.N0720.N1290.d004137 q (_root_.GD.N0232.N0720.N1368.d020208 z w u)
        (fun t ↦ (t : ℝ) * (1 - (t : ℝ))) mu) 0 := by
  calc
    _ = deriv (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z w (u + v)) 0 := by
      simpa only [add_zero] using
        (deriv_comp_const_add (fun v ↦ _root_.GD.N0232.N0720.N1368.d020209 q mu z w v) u 0).symm
    _ = _ := congrArg (fun f : ℝ → ℝ ↦ deriv f 0) (_root_.GD.N0232.N0720.N1368.d020214 q mu z w u)



theorem d020218 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 q mu) z w u =
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1368.d020208 z w u) mu := by
  unfold _root_.GD.N0232.N0720.N1368.d020210
  rw [_root_.GD.N0232.N0720.N1368.d020215, _root_.GD.N0232.N0720.N1368.d020216, _root_.GD.N0232.N0720.N1368.d020217]
  rfl

theorem d020219 (center epsilon : ℝ) :
    _root_.GD.N0232.N0720.N1368.d020208 (1 + epsilon * center) (1 - epsilon * (1 - center)) 0 =
      _root_.GD.N0232.N0720.N1290.d004147 center epsilon := by
  funext t
  unfold _root_.GD.N0232.N0720.N1368.d020208 _root_.GD.N0232.N0720.N1290.d004147
  ring

theorem d020220 (center : ℝ) :
    ∀ᶠ epsilon in nhds 0,
      0 < 1 + epsilon * center ∧ 0 < 1 - epsilon * (1 - center) := by
  have hzero : Continuous (fun _ : ℝ ↦ (0 : ℝ)) := continuous_const
  have hleft : Continuous (fun epsilon : ℝ ↦ 1 + epsilon * center) := by fun_prop
  have hright : Continuous (fun epsilon : ℝ ↦ 1 - epsilon * (1 - center)) := by fun_prop
  have ho : IsOpen {epsilon : ℝ |
      0 < 1 + epsilon * center ∧ 0 < 1 - epsilon * (1 - center)} :=
    (isOpen_lt hzero hleft).inter (isOpen_lt hzero hright)
  exact ho.eventually_mem (by constructor <;> norm_num)



theorem d020221
    (q center : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    (hF : ∀ z w : ℝ, 0 < z → 0 < w →
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 q mu) z w 0 = 0) :
    ∀ᶠ epsilon in nhds 0,
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) mu = 0 := by
  filter_upwards [_root_.GD.N0232.N0720.N1368.d020220 center] with epsilon he
  have h := hF (1 + epsilon * center) (1 - epsilon * (1 - center)) he.1 he.2
  rw [_root_.GD.N0232.N0720.N1368.d020218, _root_.GD.N0232.N0720.N1368.d020219] at h
  exact h



theorem d020222
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      _root_.GD.N0232.N0720.N1398.d019601 d x = _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) mu) :
    ∃ z w : ℝ, 0 < z ∧ 0 < w ∧
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 (5 / 2) mu) z w 0 ≠ 0 := by
  by_contra hnone
  have hzero : ∀ z w : ℝ, 0 < z → 0 < w →
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 (5 / 2) mu) z w 0 = 0 := by
    intro z w hz hw
    by_contra hne
    exact hnone ⟨z, w, hz, hw, hne⟩
  apply _root_.GD.N0232.N0720.N1402.d020207 hd mu hpost
  exact _root_.GD.N0232.N0720.N1368.d020221
    (5 / 2) (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) mu hzero




theorem d020223 (g : ℝ → ℝ → ℝ → ℝ) (z w u : ℝ) :
    _root_.GD.N0232.N0720.N1368.d020210 (fun z w u ↦ 1 - g w z u) z w u =
      -_root_.GD.N0232.N0720.N1368.d020210 g w z u := by
  unfold _root_.GD.N0232.N0720.N1368.d020210
  simp only [deriv_const_sub]
  ring

end
end GD.N0232.N0720.N1368

#print axioms _root_.GD.N0232.N0720.N1368.d020218
#print axioms _root_.GD.N0232.N0720.N1368.d020221
#print axioms _root_.GD.N0232.N0720.N1368.d020222
#print axioms _root_.GD.N0232.N0720.N1368.d020223
