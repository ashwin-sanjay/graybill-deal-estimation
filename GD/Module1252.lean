import GD.Module1240
import GD.Module1251
import GD.Module0202
import Mathlib.Analysis.Calculus.Deriv.Prod















open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace GD.N0232.N0720.N1270

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1265 _root_.GD.N0232.N0720.N1271
open _root_.GD.N0232.N0720.N1290 _root_.GD.N0232.N0720.N1368
open _root_.GD.N0232.N0720.N1352 _root_.GD.N0232.N0720.N1351

def d020224 : Set _root_.GD.N0232.N0720.N1352.d002739 := {x | 0 < x 2 ∧ 0 < x 3}

theorem d020225 : IsOpen _root_.GD.N0232.N0720.N1270.d020224 := by
  change IsOpen {x : _root_.GD.N0232.N0720.N1352.d002739 | 0 < x 2 ∧ 0 < x 3}
  exact (isOpen_lt continuous_const
    (show Continuous (fun x : _root_.GD.N0232.N0720.N1352.d002739 ↦ x 2) by fun_prop)).inter
    (isOpen_lt continuous_const
      (show Continuous (fun x : _root_.GD.N0232.N0720.N1352.d002739 ↦ x 3) by fun_prop))

def d020226 (z w : ℝ) : _root_.GD.N0232.N0720.N1352.d002739 := ![0, 0, z, w]

theorem d020227 {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    _root_.GD.N0232.N0720.N1270.d020226 z w ∈ _root_.GD.N0232.N0720.N1270.d020224 := ⟨hz, hw⟩

@[simp] theorem d020228 (z w : ℝ) : _root_.GD.N0232.N0720.N1352.d002742 (_root_.GD.N0232.N0720.N1270.d020226 z w) = 0 := by
  simp [_root_.GD.N0232.N0720.N1352.d002742, _root_.GD.N0232.N0720.N1270.d020226]

@[simp] theorem d020229 (z w : ℝ) :
    _root_.GD.N0232.N0720.N1351.d002814 (_root_.GD.N0232.N0720.N1270.d020226 z w) = ![z, w, 0] := by
  simp [_root_.GD.N0232.N0720.N1351.d002814, _root_.GD.N0232.N0720.N1270.d020226, _root_.GD.N0232.N0720.N1352.d002742]



def d020230 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (p : _root_.GD.N0232.N0720.N1351.d002812) : ℝ :=
  1 - _root_.GD.N0232.N0720.N1368.d020209 (5 / 2) mu (p 1) (p 0) (p 2)

private theorem d020231 (z w u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (![v, w, u] : _root_.GD.N0232.N0720.N1351.d002812)) (_root_.GD.N0232.N0720.N1351.d002813 0) z := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using! hasDerivAt_id z
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using hasDerivAt_const z w
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using hasDerivAt_const z u

private theorem d020232 (z w u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (![z, v, u] : _root_.GD.N0232.N0720.N1351.d002812)) (_root_.GD.N0232.N0720.N1351.d002813 1) w := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using hasDerivAt_const w z
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using! hasDerivAt_id w
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using hasDerivAt_const w u

private theorem d020233 (z w u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (![z, w, v] : _root_.GD.N0232.N0720.N1351.d002812)) (_root_.GD.N0232.N0720.N1351.d002813 2) u := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using hasDerivAt_const u z
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using hasDerivAt_const u w
  · simpa [_root_.GD.N0232.N0720.N1351.d002813] using! hasDerivAt_id u

theorem d020234 {g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ} {z w u : ℝ}
    (hg : DifferentiableAt ℝ g ![z, w, u]) :
    _root_.GD.N0232.N0720.N1351.d002819 g 0 ![z, w, u] = deriv (fun v ↦ g ![v, w, u]) z ∧
    _root_.GD.N0232.N0720.N1351.d002819 g 1 ![z, w, u] = deriv (fun v ↦ g ![z, v, u]) w ∧
    _root_.GD.N0232.N0720.N1351.d002819 g 2 ![z, w, u] = deriv (fun v ↦ g ![z, w, v]) u := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1351.d002819, Function.comp_def] using
      (hg.hasFDerivAt.comp_hasDerivAt z (_root_.GD.N0232.N0720.N1270.d020231 z w u)).deriv.symm
  · simpa only [_root_.GD.N0232.N0720.N1351.d002819, Function.comp_def] using
      (hg.hasFDerivAt.comp_hasDerivAt w (_root_.GD.N0232.N0720.N1270.d020232 z w u)).deriv.symm
  · simpa only [_root_.GD.N0232.N0720.N1351.d002819, Function.comp_def] using
      (hg.hasFDerivAt.comp_hasDerivAt u (_root_.GD.N0232.N0720.N1270.d020233 z w u)).deriv.symm

structure d020235 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) where
  domain : Set _root_.GD.N0232.N0720.N1351.d002812
  isOpen_domain : IsOpen domain
  smooth : ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1270.d020230 mu) domain
  mapsTo : MapsTo _root_.GD.N0232.N0720.N1351.d002814 _root_.GD.N0232.N0720.N1270.d020224 domain

def d020236 {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} (a : _root_.GD.N0232.N0720.N1270.d020235 mu) :
    _root_.GD.N0232.N0720.N1352.d002752 _root_.GD.N0232.N0720.N1270.d020224 :=
  _root_.GD.N0232.N0720.N1351.d002824 a.isOpen_domain (_root_.GD.N0232.N0720.N1270.d020230 mu) a.smooth a.mapsTo



theorem d020237 {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} (a : _root_.GD.N0232.N0720.N1270.d020235 mu)
    {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    _root_.GD.N0232.N0720.N1352.d002762 (_root_.GD.N0232.N0720.N1270.d020236 a).G (_root_.GD.N0232.N0720.N1270.d020236 a).Gz
      (_root_.GD.N0232.N0720.N1270.d020236 a).Gw (_root_.GD.N0232.N0720.N1270.d020236 a).Gu (_root_.GD.N0232.N0720.N1270.d020226 w z) =
        -_root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 (5 / 2) mu) z w 0 := by
  have hp : (![w, z, 0] : _root_.GD.N0232.N0720.N1351.d002812) ∈ a.domain := by
    simpa only [_root_.GD.N0232.N0720.N1270.d020229] using a.mapsTo (_root_.GD.N0232.N0720.N1270.d020227 hw hz)
  have hg := (a.smooth.contDiffAt (a.isOpen_domain.mem_nhds hp)).differentiableAt (by simp)
  obtain ⟨h0, h1, h2⟩ := _root_.GD.N0232.N0720.N1270.d020234 hg
  have heq : (fun z w u ↦ _root_.GD.N0232.N0720.N1270.d020230 mu ![z, w, u]) =
      (fun z w u ↦ 1 - _root_.GD.N0232.N0720.N1368.d020209 (5 / 2) mu w z u) := by
    funext z w u
    rfl
  calc
    _ = _root_.GD.N0232.N0720.N1368.d020210 (fun z w u ↦ _root_.GD.N0232.N0720.N1270.d020230 mu ![z, w, u]) w z 0 := by
      simp only [_root_.GD.N0232.N0720.N1352.d002762,
        _root_.GD.N0232.N0720.N1270.d020236, _root_.GD.N0232.N0720.N1351.d002824,
        _root_.GD.N0232.N0720.N1351.d002820, Function.comp_apply, _root_.GD.N0232.N0720.N1270.d020229,
        _root_.GD.N0232.N0720.N1368.d020210, h0, h1, h2]
    _ = _ := by rw [heq, _root_.GD.N0232.N0720.N1368.d020223]



structure d020238 (degree : ℕ) (g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ) where
  M : _root_.GD.N0232.N0720.N1352.d002739 → ℝ
  N : _root_.GD.N0232.N0720.N1352.d002739 → ℝ
  smooth_M : ContDiffOn ℝ ∞ M _root_.GD.N0232.N0720.N1270.d020224
  positive_M : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224, 0 < M x
  numerator : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224, N x = _root_.GD.N0232.N0720.N1352.d002804 (g ∘ _root_.GD.N0232.N0720.N1351.d002814) x * M x
  pde : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224,
    fderiv ℝ N x (_root_.GD.N0232.N0720.N1352.d002740 2) = x 0 * fderiv ℝ M x (_root_.GD.N0232.N0720.N1352.d002740 2) - fderiv ℝ M x (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
    fderiv ℝ N x (_root_.GD.N0232.N0720.N1352.d002740 3) = x 1 * fderiv ℝ M x (_root_.GD.N0232.N0720.N1352.d002740 3) - fderiv ℝ M x (_root_.GD.N0232.N0720.N1352.d002740 1)
  homogeneous : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224, ∀ a : ℝ, 0 < a →
    a ^ degree * M (_root_.GD.N0232.N0720.N1352.d002795 x a) = M x



def d020239 : Prop :=
  ∀ mu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131,
    Nonempty (_root_.GD.N0232.N0720.N1270.d020235 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)) ∧
      Nonempty (_root_.GD.N0232.N0720.N1270.d020238 5 (_root_.GD.N0232.N0720.N1270.d020230 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)))




def d020240 : Prop :=
  ∀ (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ), _root_.GD.N0232.N0720.N1159.d014660 2 2 d →
    ∀ mu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131,
      (_root_.GD.N0232.N0720.N1398.d019601 d =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦
        _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)) →
      Nonempty (_root_.GD.N0232.N0720.N1270.d020238 6 (_root_.GD.N0232.N0720.N1270.d020230 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)))

theorem d020241
    (haffine : _root_.GD.N0232.N0720.N1270.d020239) (hscale : _root_.GD.N0232.N0720.N1270.d020240)
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) : False := by
  obtain ⟨mu, hpost⟩ := _root_.GD.N0232.N0720.N1265.d020142 hd
  obtain ⟨z, w, hz, hw, hF⟩ := _root_.GD.N0232.N0720.N1368.d020222
    hd (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) hpost
  obtain ⟨⟨a⟩, ⟨m0⟩⟩ := haffine mu
  obtain ⟨m1⟩ := hscale d hd mu hpost
  let H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ := fun x ↦ m1.M x / m0.M x
  have hHinf : ContDiffOn ℝ ∞ H _root_.GD.N0232.N0720.N1270.d020224 :=
    m1.smooth_M.fun_div m0.smooth_M (fun x hx ↦ (m0.positive_M x hx).ne')
  have hH : ContDiffOn ℝ 2 H _root_.GD.N0232.N0720.N1270.d020224 := (contDiffOn_infty.mp hHinf) 2
  have hx := _root_.GD.N0232.N0720.N1270.d020227 hw hz
  apply _root_.GD.N0232.N0720.N1352.d002807 _root_.GD.N0232.N0720.N1270.d020225 (_root_.GD.N0232.N0720.N1270.d020236 a)
    hH m0.smooth_M m1.smooth_M
    (fun x hx ↦ (m0.positive_M x hx).ne')
    (fun x hx ↦ (div_mul_cancel₀ (m1.M x) (m0.positive_M x hx).ne').symm)
    m0.numerator m1.numerator m0.pde m1.pde hx (_root_.GD.N0232.N0720.N1270.d020228 w z)
  · rw [_root_.GD.N0232.N0720.N1270.d020237 a hz hw]
    exact neg_ne_zero.mpr hF
  · exact (m1.positive_M _ hx).ne'
  · filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with r hr
    exact ⟨m0.homogeneous _ hx r hr, m1.homogeneous _ hx r hr⟩



theorem d020242
    (haffine : _root_.GD.N0232.N0720.N1270.d020239) (hscale : _root_.GD.N0232.N0720.N1270.d020240) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  rintro ⟨d, hd⟩
  exact _root_.GD.N0232.N0720.N1270.d020241 haffine hscale hd



theorem d020243
    (haffine : _root_.GD.N0232.N0720.N1270.d020239) (hscale : _root_.GD.N0232.N0720.N1270.d020240)
    (seed : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0720.N1080.d014182 2 2) seed.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega))) :
    ∃ g, 0 < _root_.GD.N0232.N0720.N1159.d014647 2 2 seed g :=
  _root_.GD.N0232.N0720.N1159.d014668
    2 2 (by omega) (by omega)
    (_root_.GD.N0232.N0720.N1270.d020242 haffine hscale) seed hstrict

end
end GD.N0232.N0720.N1270

#print axioms _root_.GD.N0232.N0720.N1270.d020237
#print axioms _root_.GD.N0232.N0720.N1270.d020242
#print axioms _root_.GD.N0232.N0720.N1270.d020243
