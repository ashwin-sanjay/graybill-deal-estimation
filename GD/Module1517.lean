import GD.Module1516
import GD.Module1513
import GD.Module0528

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0024.N0282

noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0024.N0277 _root_.GD.N0024.N0281 _root_.GD.N0024.N0278

theorem d023609
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (V : ℝ)
    (hcap : ∀ t : _root_.GD.N0024.N0277.d007878, _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0281.d023601 g t ≤ V)
    (hbaseline : ∀ t : _root_.GD.N0024.N0277.d007878,
      _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0281.d023601 g t ≤ _root_.GD.N0024.N0278.d023551 t.1)
    (hminimax : ∀ f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable f →
      (∀ z, f z ∈ Icc (0 : ℝ) 1) →
      ∀ ε : ℝ, 0 < ε → ∃ t, V - ε < _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0281.d023601 f t) : False := by
  have hQ : ∀ t : _root_.GD.N0024.N0277.d007878,
      _root_.GD.N0024.N0281.d023601 t ≪ _root_.GD.N0024.N0281.d023601 _root_.GD.N0024.N0276.d007902 := by
    intro t
    exact _root_.GD.N0232.N0720.N1436.d013292
      (by norm_num) (by norm_num) t.2.1 t.2.2
      _root_.GD.N0024.N0276.d007902.2.1 _root_.GD.N0024.N0276.d007902.2.2
  have hV : 0 < V := _root_.GD.N0024.N0276.d007903 _root_.GD.N0024.N0281.d023601 hQ g hg hb V hcap
  obtain ⟨d, h, hd, hdhalf, hh, htail⟩ := _root_.GD.N0024.N0278.d023575 V hV
  exact _root_.GD.N0024.N0281.d023608 g hg hb d V h hd hdhalf hh hcap
    (fun t ht => (hbaseline t).trans (htail t ht)) hminimax

#print axioms _root_.GD.N0024.N0282.d023609

end
end GD.N0024.N0282
