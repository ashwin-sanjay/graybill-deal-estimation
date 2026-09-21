import GD.Module1557
import GD.Module1401

































set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal

namespace GD.N0106.N0428.N0763

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0100.N0347
open _root_.GD.N0178 _root_.GD.N0180
open _root_.GD.N0163 _root_.GD.N0172 _root_.GD.N0173


theorem d024060 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0100.N0347.d024054 3 3 theta =
      min (theta.scale₁ ^ 2 / 3) (theta.scale₂ ^ 2 / 3) := by
  simp [_root_.GD.N0100.N0347.d024054]



def d024061 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) : _root_.GD.N0172.d022466 :=
  ⟨fun x => g x.1, hg.comp measurable_subtype_coe, fun x => hb x.1⟩


theorem d024062 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0163.d022211 (_root_.GD.N0106.N0428.N0763.d024061 g hg hb).1 =ᵐ[_root_.GD.N0232.N0720.N1436.d013288] g := by
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
  exact _root_.GD.N0163.d022212 (_root_.GD.N0106.N0428.N0763.d024061 g hg hb).1 ⟨p, hp⟩




theorem d024063 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (hcap : (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 t) ≤
      (min t.1 (1 - t.1) / max t.1 (1 - t.1)) * t.1 * (1 - t.1)) :
    _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 (_root_.GD.N0106.N0428.N0763.d024061 g hg hb).1) ≤ _root_.GD.N0173.d022532 t := by
  have hpos : 0 < (t : ℝ) * (1 - t) := mul_pos t.property.1 (sub_pos.mpr t.property.2)
  have hae : (fun p : _root_.GD.N0232.N0720.N1436.d013217 =>
        _root_.GD.N0178.d007131 t p.1 p.2 * (_root_.GD.N0163.d022211 (_root_.GD.N0106.N0428.N0763.d024061 g hg hb).1 p - t) ^ 2)
      =ᵐ[_root_.GD.N0232.N0720.N1436.d013288] (fun p => _root_.GD.N0178.d007131 t p.1 p.2 * (g p - t) ^ 2) := by
    filter_upwards [_root_.GD.N0106.N0428.N0763.d024062 g hg hb] with p hp
    rw [hp]
  unfold _root_.GD.N0180.d022173
  rw [integral_congr_ae hae, _root_.GD.N0180.d022172 t (fun p => (g p - t) ^ 2), _root_.GD.N0173.d022532,
    div_le_iff₀ hpos]
  calc (∫ p, (g p - (t : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 t)
      ≤ (min t.1 (1 - t.1) / max t.1 (1 - t.1)) * t.1 * (1 - t.1) := hcap
    _ = min (t : ℝ) (1 - t) / max (t : ℝ) (1 - t) * ((t : ℝ) * (1 - t)) := by ring



theorem d024064
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d) :
    ¬ ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 3 3 theta d ≤ ENNReal.ofReal (_root_.GD.N0100.N0347.d024054 3 3 theta) := by
  intro hbound
  obtain ⟨g, hg, hb, hcap⟩ :=
    _root_.GD.N0100.N0347.d024059 3 3 (by norm_num) (by norm_num) d hd hbound
  exact _root_.GD.N0173.d022548
    ⟨_root_.GD.N0106.N0428.N0763.d024061 g hg hb, fun t => _root_.GD.N0106.N0428.N0763.d024063 g hg hb t (hcap t)⟩


theorem d024065
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d) :
    ¬ ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 theta d ≤
      ENNReal.ofReal (min (theta.scale₁ ^ 2 / 3) (theta.scale₂ ^ 2 / 3)) := by
  intro h
  apply _root_.GD.N0106.N0428.N0763.d024064 d hd
  intro theta
  rw [_root_.GD.N0106.N0428.N0763.d024060]
  exact h theta



theorem d024066
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d) :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      ENNReal.ofReal (min (theta.scale₁ ^ 2 / 3) (theta.scale₂ ^ 2 / 3)) <
        _root_.GD.N0232.N0720.N1080.d014197 3 3 theta d := by
  by_contra hcontra
  apply _root_.GD.N0106.N0428.N0763.d024065 d hd
  intro theta
  exact not_lt.mp fun hlt => hcontra ⟨theta, hlt⟩

end

end GD.N0106.N0428.N0763

#print axioms _root_.GD.N0106.N0428.N0763.d024063
#print axioms _root_.GD.N0106.N0428.N0763.d024064
#print axioms _root_.GD.N0106.N0428.N0763.d024065
#print axioms _root_.GD.N0106.N0428.N0763.d024066
