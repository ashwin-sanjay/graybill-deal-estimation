import GD.Module1257
import GD.Module1274












open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace GD.N0232.N0720.N1325

open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315 (d019850)
open _root_.GD.N0232.N0720.N1327
open _root_.GD.N0232.N0720.N1322 (d020080)
open _root_.GD.N0232.N0720.N1323 _root_.GD.N0232.N0720.N1343
open _root_.GD.N0232.N0720.N1382 (d004652)
open _root_.GD.N0232.N0720.N1270 (d020238)

noncomputable section

abbrev d020614 := _root_.GD.N0232.N0720.N1290.d004131
abbrev d020615 := _root_.GD.N0232.N0720.N1343.d020318
abbrev d020616 := _root_.GD.N0232.N0720.N1343.d020319

theorem d020617 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d)
    (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1325.d020614)
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦ _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n)
      (_root_.GD.N0232.N0720.N1336.d013420 m n x) (μ : Measure _root_.GD.N0232.N0720.N1325.d020614)) :
    Nonempty (_root_.GD.N0232.N0720.N1270.d020238 (m + n + 2)
      (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) (μ : Measure _root_.GD.N0232.N0720.N1325.d020614))) := by
  obtain ⟨gs, ν, hgs, _hbs, hrep_s, hν, hscale⟩ :=
    _root_.GD.N0232.N0720.N1343.d020326
      m n k hdim hm hn hd
  have hcommon := _root_.GD.N0232.N0720.N1327.d020596 m n k hdim hgs hg
    (fun θ ↦ (hrep_s θ).symm) hrep
  have hae : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)),
      x ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim →
      _root_.GD.N0232.N0720.N1323.d020304 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) /
          _root_.GD.N0232.N0720.N1323.d020303 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) =
        _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x := by
    filter_upwards [hscale, hcommon] with x hs hc
    intro hx
    rw [hdim, ← _root_.GD.N0232.N0720.N1343.d020323]
    exact (hs hx).trans hc
  have hcontinuous : ContinuousOn (fun x : _root_.GD.N0232.N0720.N1325.d020616 ↦
      _root_.GD.N0232.N0720.N1323.d020304 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) x /
        _root_.GD.N0232.N0720.N1323.d020303 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) x) _root_.GD.N0232.N0720.N1382.d004652 :=
    (_root_.GD.N0232.N0720.N1323.d020306 (m + n) _ hν).continuousOn.div
      (_root_.GD.N0232.N0720.N1323.d020305 (m + n) _ hν).continuousOn
      (fun x hx ↦ (_root_.GD.N0232.N0720.N1323.d020307 (m + n) _ hν hx).ne')
  have heq := _root_.GD.N0232.N0720.N1327.d020613 m n k hdim hm hn hd hg hb hrep
    (μ : Measure _root_.GD.N0232.N0720.N1325.d020614) hpost hcontinuous hae
  exact ⟨_root_.GD.N0232.N0720.N1323.d020317 (m + n) ν hν (fun x hx ↦ heq hx)⟩

end
end GD.N0232.N0720.N1325

#print axioms _root_.GD.N0232.N0720.N1325.d020617
