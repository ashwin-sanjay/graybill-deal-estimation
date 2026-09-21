import GD.Module1416
import GD.Module1851
import GD.Module1359
import GD.Module1541
import GD.Module1854

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0029
noncomputable section
open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0024 _root_.GD.N0024.N0277
open _root_.GD.N0023
open _root_.GD.N0046.N0305



theorem d030441
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (C : ℝ)
    (hcap : ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 2 5 (by decide) (by decide)) g t ≤ C)
    (hbase : ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 2 5 (by decide) (by decide)) g t ≤
      _root_.GD.N0023.N0258.d021868 2 5 t) : False := by
  have hraw : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z - (t : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 t) ≤ C * (t : ℝ) * (1 - (t : ℝ)) := by
    intro t
    have hh := (div_le_iff₀ (_root_.GD.N0024.N0277.d007880 t)).mp (hcap t)
    simpa only [_root_.GD.N0024.N0277.d007882, _root_.GD.N0024.N0277.d007881, _root_.GD.N0024.N0277.d007879, mul_assoc, _root_.GD.N0023.N0261.d021897, _root_.GD.N0232.N0720.N1441.d013678] using hh
  obtain ⟨η, hη, hbad⟩ := _root_.GD.N0028.d021930
    g hg (B := 1) (fun z => by rw [abs_of_nonneg (hb z).1]; exact (hb z).2) C hraw
  obtain ⟨δ, hδ, hsmall⟩ := _root_.GD.N0023.N0258.d021878
    (_root_.GD.N0023.N0258.d021868 2 5)
    (_root_.GD.N0065.d022701 2 5 (by decide) (by decide)) η hη
  obtain ⟨t, ht, hstrict⟩ := hbad δ hδ
  have hh := (div_le_iff₀ (_root_.GD.N0024.N0277.d007880 t)).mp ((hbase t).trans (hsmall t ht))
  have hupper : (∫ z, (g z - (t : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 t) ≤
      η * (t : ℝ) * (1 - (t : ℝ)) := by
    simpa only [_root_.GD.N0024.N0277.d007882, _root_.GD.N0024.N0277.d007881, _root_.GD.N0024.N0277.d007879, mul_assoc, _root_.GD.N0023.N0261.d021897, _root_.GD.N0232.N0720.N1441.d013678] using hh
  have hs := mul_le_mul_of_nonneg_left t.2.2.le
    (mul_nonneg hη.le (sub_pos.mpr t.2.2).le)
  nlinarith


theorem d030442 : _root_.GD.N0046.N0305.d030202 2 5 (by decide) (by decide) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hK
  let v := (_root_.GD.N0232.N0720.N1256.d015549 2 5).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hvalue : _root_.GD.N0232.N0720.N1256.d015549 2 5 = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal _root_.GD.N0030.d023898).symm
  obtain ⟨g, hg, hb, hbound⟩ := _root_.GD.N0024.N0270.d030252
    2 5 (by decide) (by decide) v hv hvalue hK
  exact _root_.GD.N0029.d030441 g hg hb (v - 1)
    (_root_.GD.N0023.N0262.d021914 2 5 (by decide) (by decide)
      g hg hb v hv (fun θ => (hbound θ).1))
    (_root_.GD.N0023.N0262.d021920 2 5 (by decide) (by decide)
      g hg hb (fun θ => (hbound θ).2))

theorem d030443 :
    _root_.GD.N0232.N0720.N1256.d015549 2 5 < _root_.GD.N0022.N0255.d030394 2 5 :=
  (_root_.GD.N0022.N0255.d030398
    2 5 (by decide) (by decide)).mp _root_.GD.N0029.d030442

theorem d030444 :
    ¬ _root_.GD.N0232.N0720.N1226.d015578 2 5 := by
  intro h
  obtain ⟨p, hp, _⟩ := (_root_.GD.N0046.N0305.d030214
    2 5 (by decide) (by decide)).mp h
  rw [_root_.GD.N0029.d030442] at hp
  exact hp

theorem d030445 : _root_.GD.N0046.N0305.d030202 5 2 (by decide) (by decide) = ∅ :=
  _root_.GD.N0037.d030435 5 2 (by decide) (by decide)
    _root_.GD.N0029.d030442

theorem d030446 :
    _root_.GD.N0232.N0720.N1256.d015549 5 2 < _root_.GD.N0022.N0255.d030394 5 2 :=
  (_root_.GD.N0022.N0255.d030398
    5 2 (by decide) (by decide)).mp _root_.GD.N0029.d030445

theorem d030447 :
    ¬ _root_.GD.N0232.N0720.N1226.d015578 5 2 := by
  intro h
  obtain ⟨p, hp, _⟩ := (_root_.GD.N0046.N0305.d030214
    5 2 (by decide) (by decide)).mp h
  rw [_root_.GD.N0029.d030445] at hp
  exact hp

end
end GD.N0029

#print axioms _root_.GD.N0029.d030441
#print axioms _root_.GD.N0029.d030442
#print axioms _root_.GD.N0029.d030443
#print axioms _root_.GD.N0029.d030444
#print axioms _root_.GD.N0029.d030445
#print axioms _root_.GD.N0029.d030446
#print axioms _root_.GD.N0029.d030447
