import GD.Module1386

















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0169
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0178 _root_.GD.N0180

def d022354 (eta a b c : ℝ) : Set _root_.GD.N0232.N0720.N1436.d013217 :=
  Ioc eta (1 - eta) ×ˢ Ioc (a / c) (b / c)

def d022355 (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0178.d007131 t p.1 p.2 * (_root_.GD.N0163.d022211 g p - t) ^ 2

def d022356 (eta a b c : ℝ) (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) : ℝ :=
  ∫ u in eta..(1 - eta), ∫ x in a..b,
    _root_.GD.N0178.d007131 t u (x / c) / c *
      (_root_.GD.N0163.d022211 g (u, x / c) - t) ^ 2

theorem d022357 (eta a b c : ℝ) :
    MeasurableSet (_root_.GD.N0169.d022354 eta a b c) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem d022358 {eta a b c : ℝ} (heta : 0 < eta) (ha : 0 < a)
    (hc : 0 < c) : _root_.GD.N0169.d022354 eta a b c ⊆ _root_.GD.N0232.N0720.N1436.d013218 := by
  intro p hp
  exact ⟨⟨heta.trans hp.1.1, by linarith [hp.1.2]⟩,
    (div_pos ha hc).trans hp.2.1⟩


theorem d022359 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (_root_.GD.N0169.d022355 t g) _root_.GD.N0232.N0720.N1436.d013288 := by
  have hB : ∀ p, |_root_.GD.N0163.d022211 g p| ≤ 1 := by
    intro p
    have hp := _root_.GD.N0163.d022214 g h01 p
    rw [abs_of_nonneg hp.1]
    exact hp.2
  exact _root_.GD.N0180.d022174 t _
    (_root_.GD.N0163.d022213 g hg) hB

theorem d022360 (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    {p : _root_.GD.N0232.N0720.N1436.d013217} (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 ≤ _root_.GD.N0169.d022355 t g p :=
  mul_nonneg (_root_.GD.N0178.d007141 t.property.1 t.property.2 hp.1.1.le hp.1.2.le hp.2)
    (sq_nonneg _)

theorem d022361 {eta a b c : ℝ} (heta : 0 < eta) (ha : 0 < a)
    (hc : 0 < c)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (_root_.GD.N0169.d022355 t g) (_root_.GD.N0169.d022354 eta a b c) volume := by
  have hi : IntegrableOn (_root_.GD.N0169.d022355 t g) _root_.GD.N0232.N0720.N1436.d013218 volume :=
    _root_.GD.N0169.d022359 t g hg h01
  exact hi.mono_set (_root_.GD.N0169.d022358 heta ha hc)


theorem d022362 {eta a b c : ℝ} (heta : 0 < eta) (ha : 0 < a)
    (hc : 0 < c)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ p in _root_.GD.N0169.d022354 eta a b c, _root_.GD.N0169.d022355 t g p) ≤
      _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 g) := by
  have hi : IntegrableOn (_root_.GD.N0169.d022355 t g) _root_.GD.N0232.N0720.N1436.d013218 volume :=
    _root_.GD.N0169.d022359 t g hg h01
  have hn : 0 ≤ᵐ[volume.restrict _root_.GD.N0232.N0720.N1436.d013218] _root_.GD.N0169.d022355 t g := by
    filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
    exact _root_.GD.N0169.d022360 t g hp
  exact setIntegral_mono_set hi hn
    (ae_of_all _ (fun p hp => _root_.GD.N0169.d022358 heta ha hc hp))


theorem d022363 {eta a b c : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0169.d022356 eta a b c t g =
      ∫ p in _root_.GD.N0169.d022354 eta a b c, _root_.GD.N0169.d022355 t g p := by
  have hwin : eta ≤ 1 - eta := by linarith
  have hswin : a / c ≤ b / c := div_le_div_of_nonneg_right hab hc.le
  have hprod := MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (_root_.GD.N0169.d022355 t g)
    (_root_.GD.N0169.d022361 (b := b) heta ha hc t g hg h01)
  have hs (u : ℝ) :
      (∫ x in a..b, _root_.GD.N0178.d007131 t u (x / c) / c *
        (_root_.GD.N0163.d022211 g (u, x / c) - t) ^ 2) =
      ∫ s in (a / c)..(b / c), _root_.GD.N0169.d022355 t g (u, s) := by
    have h := intervalIntegral.inv_smul_integral_comp_div
      (a := a) (b := b) (fun s => _root_.GD.N0169.d022355 t g (u, s)) c
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul] at h
    calc
      _ = ∫ x in a..b, c⁻¹ * _root_.GD.N0169.d022355 t g (u, x / c) := by
        apply intervalIntegral.integral_congr
        intro x _
        unfold _root_.GD.N0169.d022355
        simp only [div_eq_mul_inv]
        ring
      _ = _ := h
  unfold _root_.GD.N0169.d022356
  calc
    _ = ∫ u in eta..(1 - eta),
        ∫ s in (a / c)..(b / c), _root_.GD.N0169.d022355 t g (u, s) :=
      intervalIntegral.integral_congr (fun u _ => hs u)
    _ = ∫ p in _root_.GD.N0169.d022354 eta a b c, _root_.GD.N0169.d022355 t g p := by
      simpa only [_root_.GD.N0169.d022354, MeasureTheory.Measure.volume_eq_prod,
        intervalIntegral.integral_of_le hwin,
        intervalIntegral.integral_of_le hswin] using hprod.symm


theorem d022364 {eta a b c : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0169.d022356 eta a b c t g ≤ _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 g) := by
  rw [_root_.GD.N0169.d022363 heta hhalf ha hab hc t g hg h01]
  exact _root_.GD.N0169.d022362 heta ha hc t g hg h01

end
end GD.N0169

#print axioms _root_.GD.N0169.d022357
#print axioms _root_.GD.N0169.d022358
#print axioms _root_.GD.N0169.d022359
#print axioms _root_.GD.N0169.d022360
#print axioms _root_.GD.N0169.d022361
#print axioms _root_.GD.N0169.d022362
#print axioms _root_.GD.N0169.d022363
#print axioms _root_.GD.N0169.d022364
