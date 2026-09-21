import GD.Module0420









open MeasureTheory Set

namespace GD.N0143

noncomputable section

open _root_.GD.N0124




theorem d006698
    (g : _root_.GD.N0124.d006387 → ℝ)
    (hg : IntegrableOn g _root_.GD.N0124.d006389 volume) :
    (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389, g p)
      =
    ∫ L : ℝ in Ioo 0 1,
      ∫ F : ℝ in Ioi 0,
        ∫ H : ℝ in Ioi 0, g (L, F, H) := by
  let s : Set ℝ := Ioo 0 1
  let t : Set ℝ := Ioi 0
  let u : Set ℝ := Ioi 0
  have hTarget :
      _root_.GD.N0124.d006389 = s ×ˢ (t ×ˢ u) := by
    ext p
    simp [_root_.GD.N0124.d006389, s, t, u, and_assoc]
  have hVolume :
      (volume : Measure _root_.GD.N0124.d006387) =
        (volume : Measure ℝ).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) := rfl
  have hg' :
      IntegrableOn g (s ×ˢ (t ×ˢ u))
        ((volume : Measure ℝ).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
    simpa [hTarget, hVolume] using hg
  have hSections :
      ∀ᵐ L ∂(volume : Measure ℝ).restrict s,
        IntegrableOn (fun p : ℝ × ℝ => g (L, p))
          (t ×ˢ u)
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hg'
    have h := hg'.prod_right_ae
    simpa [IntegrableOn] using h
  rw [hTarget, hVolume,
    MeasureTheory.setIntegral_prod g hg']
  apply integral_congr_ae
  filter_upwards [hSections] with L hL
  exact MeasureTheory.setIntegral_prod (fun p : ℝ × ℝ => g (L, p)) hL

end

end GD.N0143
