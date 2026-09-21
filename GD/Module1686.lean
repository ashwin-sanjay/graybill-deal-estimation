import GD.Module1685
import GD.Module1503
import GD.Module0547

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace GD.N0101.N0366
noncomputable section

open _root_.GD.N0101.N0365 _root_.GD.N0101.N0398 _root_.GD.N0101.N0399
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0896 _root_.GD.N0072
open _root_.GD.N0225.N0538
open _root_.GD.N0225.N0540

local instance d028471 : MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 2) := borel (_root_.GD.N0232.N0719.N0859.d010809 2)
local instance d028472 : BorelSpace (_root_.GD.N0232.N0719.N0859.d010809 2) := ⟨rfl⟩



theorem d028473 (a : Fin 2 → ℝ)
    (g : (Fin 2 → ℝ) → ℝ) (hg : Measurable g) (hpos : ∀ β, 0 < g β)
    (E : ℝ → ℝ≥0∞) (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ N : ℝ, 1 ≤ N →
      (∫⁻ β, ENNReal.ofReal (g β) ∂_root_.GD.N0101.N0365.d028458 a N) ≤ E N) : False := by
  have hmu : _root_.GD.N0101.N0365.d028464 a ≠ 0 := by
    intro h
    have hm := _root_.GD.N0101.N0365.d028465 a
    simp [h] at hm
  letI : NeZero (_root_.GD.N0101.N0365.d028464 a) := ⟨hmu⟩
  apply _root_.GD.N0222.d008140
    atTop (_root_.GD.N0101.N0365.d028464 a) (_root_.GD.N0101.N0365.d028458 a) g hg.aemeasurable E
    (ae_of_all _ hpos)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact _root_.GD.N0101.N0365.d028467 a hN
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact hbound N hN
  · exact hE




theorem d028474
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (p : (Fin 2 → ℝ) → Fin 2 → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hpnn : ∀ t i, 0 ≤ p t i)
    (E : ℝ → ℝ≥0∞) (hE : Tendsto E atTop (𝓝 0))
    (hregret : ∀ w : (Fin 2 → ℝ) → Fin 2 → ℝ,
      Measurable w → (∀ t, ∑ i, w t i = 1) → (∀ t i, 0 ≤ w t i) →
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p)) →
      ∀ N : ℝ, 1 ≤ N →
        (∫⁻ β, ENNReal.ofReal ((_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal -
          (_root_.GD.N0101.N0398.d023335 sizes hn w β).toReal) ∂_root_.GD.N0101.N0365.d028458 (_root_.GD.N0232.N0719.N0954.d009355 sizes) N) ≤ E N) :
    ¬ ∃ w : (Fin 2 → ℝ) → Fin 2 → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p) := by
  rintro ⟨w, hw, hwunit, hweak, hstrict⟩
  let v := _root_.GD.N0072.d007614 ∘ w
  have hvm : Measurable v := _root_.GD.N0072.d007625.comp hw
  have hvunit : ∀ t, ∑ i, v t i = 1 := fun t => _root_.GD.N0072.d007617 (w t) (hwunit t)
  have hvnn : ∀ t i, 0 ≤ v t i := fun t i => _root_.GD.N0072.d007616 (w t) (hwunit t) i
  have hvweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes v) ≤
      _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p) := fun θ =>
    (_root_.GD.N0072.d023444 sizes hn w hw hwunit θ).trans (hweak θ)
  have hvstrict : ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes v) <
      _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes p) := by
    obtain ⟨θ, hθ⟩ := hstrict
    exact ⟨θ, (_root_.GD.N0072.d023444 sizes hn w hw hwunit θ).trans_lt hθ⟩
  obtain ⟨hmidm, hmidunit, hmidnn, hmidstrict⟩ :=
    _root_.GD.N0225.N0538.d023465 sizes hn p v hp hvm hpunit hvunit hpnn hvnn hvweak hvstrict
  have hpf := _root_.GD.N0225.N0538.d023463 sizes hn p hp hpunit hpnn
  have hmidf := _root_.GD.N0225.N0538.d023463 sizes hn _ hmidm hmidunit hmidnn
  have hg : Measurable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal -
      (_root_.GD.N0101.N0398.d023335 sizes hn (_root_.GD.N0225.N0538.d023458 p v) β).toReal) :=
    _root_.GD.N0225.N0540.d023483 sizes (_root_.GD.N0101.N0399.d023328 sizes (fun i => by have := hn i; omega))
      (_root_.GD.N0101.N0399.d023329 sizes _) p _ hpf hmidf
  refine _root_.GD.N0101.N0366.d028473 (_root_.GD.N0232.N0719.N0954.d009355 sizes) _ hg ?_ E hE
    (hregret _ hmidm hmidunit hmidnn (fun θ => (hmidstrict θ).le))
  intro β
  exact sub_pos.mpr ((ENNReal.toReal_lt_toReal
    (hmidf.2 _) (hpf.2 _)).mpr (hmidstrict _))

end
end GD.N0101.N0366

#print axioms _root_.GD.N0101.N0366.d028473
#print axioms _root_.GD.N0101.N0366.d028474
