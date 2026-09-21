















import Mathlib
import GD.Module0408

namespace GD.N0155
open MeasureTheory


def d006305 (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * p.2, (1 - p.1) * p.2)


noncomputable def d006306 (q : ℝ × ℝ) : ℝ × ℝ := (q.1 / (q.1 + q.2), q.1 + q.2)


def d006307 : Set (ℝ × ℝ) := Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ)


def d006308 : Set (ℝ × ℝ) := Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)


lemma d006309 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0155.d006307) : _root_.GD.N0155.d006306 (_root_.GD.N0155.d006305 p) = p := by
  obtain ⟨⟨hu0, hu1⟩, hT⟩ := hp
  have hT' : p.2 ≠ 0 := ne_of_gt hT
  apply Prod.ext
  · show p.1 * p.2 / (p.1 * p.2 + (1 - p.1) * p.2) = p.1
    rw [show p.1 * p.2 + (1 - p.1) * p.2 = p.2 by ring]
    field_simp
  · show p.1 * p.2 + (1 - p.1) * p.2 = p.2
    ring


lemma d006310 {q : ℝ × ℝ} (hq : q ∈ _root_.GD.N0155.d006308) : _root_.GD.N0155.d006305 (_root_.GD.N0155.d006306 q) = q := by
  obtain ⟨ha, hb⟩ := hq
  simp only [Set.mem_Ioi] at ha hb
  have hab : (0:ℝ) < q.1 + q.2 := by linarith
  have hab' : q.1 + q.2 ≠ 0 := ne_of_gt hab
  apply Prod.ext
  · show q.1 / (q.1 + q.2) * (q.1 + q.2) = q.1
    field_simp
  · show (1 - q.1 / (q.1 + q.2)) * (q.1 + q.2) = q.2
    field_simp
    ring


lemma d006311 : _root_.GD.N0155.d006305 '' _root_.GD.N0155.d006307 = _root_.GD.N0155.d006308 := by
  ext q
  simp only [Set.mem_image, _root_.GD.N0155.d006308, _root_.GD.N0155.d006307, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, ⟨⟨hu0, hu1⟩, hT⟩, hpq⟩
    subst hpq
    simp only [_root_.GD.N0155.d006305]
    exact ⟨mul_pos hu0 hT, mul_pos (by linarith) hT⟩
  · rintro ⟨ha, hb⟩
    refine ⟨_root_.GD.N0155.d006306 q, ?_, _root_.GD.N0155.d006310 ⟨ha, hb⟩⟩
    simp only [_root_.GD.N0155.d006306]
    have hab : (0:ℝ) < q.1 + q.2 := by linarith
    refine ⟨⟨div_pos ha hab, ?_⟩, hab⟩
    rw [div_lt_one hab]; linarith


lemma d006312 : Set.InjOn _root_.GD.N0155.d006305 _root_.GD.N0155.d006307 := by
  intro p hp q hq hpq
  have h1 : _root_.GD.N0155.d006306 (_root_.GD.N0155.d006305 p) = p := _root_.GD.N0155.d006309 hp
  have h2 : _root_.GD.N0155.d006306 (_root_.GD.N0155.d006305 q) = q := _root_.GD.N0155.d006309 hq
  rw [← h1, ← h2, hpq]



noncomputable def d006313 (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.2, p.1; -p.2, 1 - p.1]).toContinuousLinearMap


theorem d006314 (p : ℝ × ℝ) :
    HasFDerivAt _root_.GD.N0155.d006305 (_root_.GD.N0155.d006313 p) p := by
  have hfst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have hconst : HasFDerivAt (fun _ : ℝ × ℝ => (1 : ℝ)) 0 p :=
    hasFDerivAt_const (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ) (1 : ℝ) p
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1 * q.2)
      (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hfst.mul hsnd
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => (1 - q.1) * q.2)
      ((1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ
        + p.2 • (0 - ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    (hconst.sub hfst).mul hsnd
  have hprod : HasFDerivAt _root_.GD.N0155.d006305
      ((p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ
          + p.2 • (0 - ContinuousLinearMap.fst ℝ ℝ ℝ))) p :=
    h1.prodMk h2
  unfold _root_.GD.N0155.d006313
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert hprod using 1
  ext <;> simp


theorem d006315 (p : ℝ × ℝ) : (_root_.GD.N0155.d006313 p).det = p.2 := by
  unfold _root_.GD.N0155.d006313
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring




theorem d006316 (G : ℝ × ℝ → ℝ)
    (hG : IntegrableOn (fun p => G (_root_.GD.N0155.d006305 p) * p.2) _root_.GD.N0155.d006307 volume) :
    (∫ a in Set.Ioi (0:ℝ), ∫ b in Set.Ioi (0:ℝ), G (a, b))
      = ∫ u in (0:ℝ)..1, ∫ T in Set.Ioi (0:ℝ), G (u*T, (1-u)*T) * T := by
  have hSmeas : MeasurableSet _root_.GD.N0155.d006307 :=
    measurableSet_Ioo.prod measurableSet_Ioi
  have hFderiv : ∀ p ∈ _root_.GD.N0155.d006307, HasFDerivWithinAt _root_.GD.N0155.d006305 (_root_.GD.N0155.d006313 p) _root_.GD.N0155.d006307 p :=
    fun p _ => (_root_.GD.N0155.d006314 p).hasFDerivWithinAt

  have h_smul_eq : ∀ p ∈ _root_.GD.N0155.d006307,
      |(_root_.GD.N0155.d006313 p).det| • G (_root_.GD.N0155.d006305 p) = G (_root_.GD.N0155.d006305 p) * p.2 := by
    intro p hp
    rw [_root_.GD.N0155.d006315, abs_of_pos hp.2, smul_eq_mul, mul_comm]

  have hG' : IntegrableOn (fun p => |(_root_.GD.N0155.d006313 p).det| • G (_root_.GD.N0155.d006305 p)) _root_.GD.N0155.d006307 volume := by
    refine hG.congr ?_
    refine (Filter.EventuallyEq.symm ?_)
    exact (ae_restrict_iff' hSmeas).mpr (Filter.Eventually.of_forall h_smul_eq)

  have hG_target : IntegrableOn G _root_.GD.N0155.d006308 volume := by
    rw [← _root_.GD.N0155.d006311]
    exact (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      hSmeas hFderiv _root_.GD.N0155.d006312 G).mpr hG'

  have h_iter_lhs :
      (∫ a in Set.Ioi (0:ℝ), ∫ b in Set.Ioi (0:ℝ), G (a, b))
        = ∫ z in _root_.GD.N0155.d006308, G z := by
    rw [show _root_.GD.N0155.d006308 = Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from rfl,
        show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        setIntegral_prod G]
    simpa [_root_.GD.N0155.d006308, show (volume : Measure (ℝ × ℝ)) =
      (volume : Measure ℝ).prod volume from rfl] using hG_target

  have h_cov :
      (∫ z in _root_.GD.N0155.d006308, G z)
        = ∫ p in _root_.GD.N0155.d006307, |(_root_.GD.N0155.d006313 p).det| • G (_root_.GD.N0155.d006305 p) := by
    rw [← _root_.GD.N0155.d006311]
    exact integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
      hSmeas hFderiv _root_.GD.N0155.d006312 G

  have h_smul_int :
      (∫ p in _root_.GD.N0155.d006307, |(_root_.GD.N0155.d006313 p).det| • G (_root_.GD.N0155.d006305 p))
        = ∫ p in _root_.GD.N0155.d006307, G (_root_.GD.N0155.d006305 p) * p.2 :=
    setIntegral_congr_fun hSmeas h_smul_eq

  have h_iter_rhs :
      (∫ p in _root_.GD.N0155.d006307, G (_root_.GD.N0155.d006305 p) * p.2)
        = ∫ u in Set.Ioo (0:ℝ) 1, ∫ T in Set.Ioi (0:ℝ),
            G (_root_.GD.N0155.d006305 (u, T)) * T := by
    rw [show _root_.GD.N0155.d006307 = Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ) from rfl,
        show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        setIntegral_prod (fun p => G (_root_.GD.N0155.d006305 p) * p.2)]
    simpa [_root_.GD.N0155.d006307, show (volume : Measure (ℝ × ℝ)) =
      (volume : Measure ℝ).prod volume from rfl] using hG

  have h_interval :
      (∫ u in Set.Ioo (0:ℝ) 1, ∫ T in Set.Ioi (0:ℝ), G (_root_.GD.N0155.d006305 (u, T)) * T)
        = ∫ u in (0:ℝ)..1, ∫ T in Set.Ioi (0:ℝ), G (u*T, (1-u)*T) * T := by
    rw [intervalIntegral.integral_of_le zero_le_one,
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rfl

  rw [h_iter_lhs, h_cov, h_smul_int, h_iter_rhs, h_interval]


noncomputable def d006317 (v1 v2 : ℝ) : ℝ × ℝ → ℝ := fun q =>
  (_root_.GD.N0155.d006193 (11 * q.2 / (11 * q.2 + 11 * q.1)) *
    (11 * q.2 / (11 * q.2 + 11 * q.1) - _root_.GD.N0155.d006267 (v2 / v1)) *
    (3 * ((v1 + v2) / (q.1 + q.2)) - 7/2)) * _root_.GD.N0155.d006293 v1 q.1 * _root_.GD.N0155.d006293 v2 q.2


noncomputable def d006318 (v1 v2 : ℝ) : ℝ × ℝ → ℝ := fun q =>
  (_root_.GD.N0155.d006193 (11 * q.2 / (11 * q.2 + 11 * q.1)) ^ 2 *
    (15 * ((v1 + v2) / (q.1 + q.2)) ^ 2 - 21 * ((v1 + v2) / (q.1 + q.2)) + 49/4)) *
    _root_.GD.N0155.d006293 v1 q.1 * _root_.GD.N0155.d006293 v2 q.2


theorem d006319 (v1 v2 : ℝ) :
    _root_.GD.N0155.d006297 v1 v2 = ∫ a in Set.Ioi (0:ℝ), ∫ b in Set.Ioi (0:ℝ), _root_.GD.N0155.d006317 v1 v2 (a, b) := rfl


theorem d006320 (v1 v2 : ℝ) :
    _root_.GD.N0155.d006299 v1 v2 =
      ∫ u in (0:ℝ)..1, ∫ T in Set.Ioi (0:ℝ), _root_.GD.N0155.d006317 v1 v2 (u*T, (1-u)*T) * T := rfl


theorem d006321 (v1 v2 : ℝ) :
    _root_.GD.N0155.d006298 v1 v2 = ∫ a in Set.Ioi (0:ℝ), ∫ b in Set.Ioi (0:ℝ), _root_.GD.N0155.d006318 v1 v2 (a, b) := rfl


theorem d006322 (v1 v2 : ℝ) :
    _root_.GD.N0155.d006300 v1 v2 =
      ∫ u in (0:ℝ)..1, ∫ T in Set.Ioi (0:ℝ), _root_.GD.N0155.d006318 v1 v2 (u*T, (1-u)*T) * T := rfl






theorem d006323 {v1 v2 : ℝ}
    (hC : IntegrableOn (fun p => _root_.GD.N0155.d006317 v1 v2 (_root_.GD.N0155.d006305 p) * p.2) _root_.GD.N0155.d006307 volume)
    (hA : IntegrableOn (fun p => _root_.GD.N0155.d006318 v1 v2 (_root_.GD.N0155.d006305 p) * p.2) _root_.GD.N0155.d006307 volume) :
    _root_.GD.N0155.d006297 v1 v2 = _root_.GD.N0155.d006299 v1 v2 ∧ _root_.GD.N0155.d006298 v1 v2 = _root_.GD.N0155.d006300 v1 v2 := by
  refine ⟨?_, ?_⟩
  · rw [_root_.GD.N0155.d006319, _root_.GD.N0155.d006320]
    exact _root_.GD.N0155.d006316 (_root_.GD.N0155.d006317 v1 v2) hC
  · rw [_root_.GD.N0155.d006321, _root_.GD.N0155.d006322]
    exact _root_.GD.N0155.d006316 (_root_.GD.N0155.d006318 v1 v2) hA











noncomputable def d006324 (v1 v2 u : ℝ) : ℝ := 5 * u / v1 + 5 * (1 - u) / v2


noncomputable def d006325 (v1 v2 : ℝ) : ℝ := min (5 / v1) (5 / v2)




noncomputable def d006326 (v1 v2 : ℝ) : ℝ :=
  (5 ^ 5 / (24 * v1 ^ 5)) * (5 ^ 5 / (24 * v2 ^ 5))

lemma d006327 {v1 v2 : ℝ} (h1 : 0 < v1) (h2 : 0 < v2) :
    0 < _root_.GD.N0155.d006325 v1 v2 := by
  unfold _root_.GD.N0155.d006325
  exact lt_min (by positivity) (by positivity)



lemma d006328 {v1 v2 u : ℝ} (_h1 : 0 < v1) (_h2 : 0 < v2)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0155.d006325 v1 v2 ≤ _root_.GD.N0155.d006324 v1 v2 u := by
  obtain ⟨hu0, hu1⟩ := hu
  have h1u : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hL : _root_.GD.N0155.d006325 v1 v2 ≤ 5 / v1 := min_le_left _ _
  have hR : _root_.GD.N0155.d006325 v1 v2 ≤ 5 / v2 := min_le_right _ _
  calc _root_.GD.N0155.d006325 v1 v2
      = u * _root_.GD.N0155.d006325 v1 v2 + (1 - u) * _root_.GD.N0155.d006325 v1 v2 := by ring
    _ ≤ u * (5 / v1) + (1 - u) * (5 / v2) :=
        add_le_add (mul_le_mul_of_nonneg_left hL hu0)
                   (mul_le_mul_of_nonneg_left hR h1u)
    _ = _root_.GD.N0155.d006324 v1 v2 u := by simp only [_root_.GD.N0155.d006324]; ring



lemma d006329 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun T : ℝ => T ^ n * Real.exp (-c * T)) (Set.Ioi 0) volume := by
  have hcne : (c ^ n) ≠ 0 := pow_ne_zero n hc.ne'

  have hcomp : IntegrableOn
      (fun T : ℝ => (c * T) ^ n * Real.exp (-(c * T))) (Set.Ioi 0) volume := by
    have : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Set.Ioi (c * 0)) volume := by
      simpa using _root_.GD.N0155.d006292 n
    exact (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => x ^ n * Real.exp (-x)) 0 hc).mpr this

  have hscaled : IntegrableOn
      (fun T : ℝ => (c ^ n)⁻¹ * ((c * T) ^ n * Real.exp (-(c * T))))
      (Set.Ioi 0) volume :=
    hcomp.const_mul ((c ^ n)⁻¹)
  refine hscaled.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
  intro T _
  simp only []
  rw [mul_pow, show -(c * T) = -c * T by ring]
  field_simp



lemma d006330 {M : ℝ → ℝ}
    (hM : IntegrableOn M (Set.Ioi 0) volume) :
    IntegrableOn (fun p : ℝ × ℝ => M p.2) _root_.GD.N0155.d006307 volume := by
  have hU : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) 1) volume :=
    integrableOn_const (C := (1 : ℝ))
      (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hprod : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * M z.2)
      ((volume.restrict (Set.Ioo (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ)))) :=
    hU.mul_prod hM
  have hSpolar_eq :
      (volume.restrict (Set.Ioo (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ)))
        = (volume : Measure (ℝ × ℝ)).restrict _root_.GD.N0155.d006307 := by
    rw [_root_.GD.N0155.d006307, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        Measure.prod_restrict]
  change Integrable (fun p : ℝ × ℝ => M p.2) ((volume : Measure (ℝ × ℝ)).restrict _root_.GD.N0155.d006307)
  rw [← hSpolar_eq]
  exact hprod.congr (Filter.Eventually.of_forall (fun _ => one_mul _))



lemma d006331 {v1 v2 u T : ℝ} (h1 : 0 < v1) (h2 : 0 < v2)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hT : 0 < T) :
    _root_.GD.N0155.d006317 v1 v2 (_root_.GD.N0155.d006305 (u, T)) * T =
      _root_.GD.N0155.d006326 v1 v2 * (_root_.GD.N0155.d006193 (1 - u) * (1 - u - _root_.GD.N0155.d006267 (v2 / v1)) *
        (u ^ 4 * (1 - u) ^ 4) *
        (3 * (v1 + v2) * T ^ 8 - (7 / 2) * T ^ 9)) *
        Real.exp (-(_root_.GD.N0155.d006324 v1 v2 u * T)) := by
  have hT0 : T ≠ 0 := hT.ne'
  have hv1 : v1 ≠ 0 := h1.ne'
  have hv2 : v2 ≠ 0 := h2.ne'
  have h11T : (11 : ℝ) * ((1 - u) * T) + 11 * (u * T) ≠ 0 := by
    rw [show (11 : ℝ) * ((1 - u) * T) + 11 * (u * T) = 11 * T by ring]
    exact mul_ne_zero (by norm_num) hT0
  have hsum : u * T + (1 - u) * T = T := by ring
  have hratio : (11 : ℝ) * ((1 - u) * T) /
      (11 * ((1 - u) * T) + 11 * (u * T)) = 1 - u := by
    rw [show (11 : ℝ) * ((1 - u) * T) + 11 * (u * T) = 11 * T by ring]
    field_simp
  have hexp :
      Real.exp (-(5 * (u * T) / v1)) * Real.exp (-(5 * ((1 - u) * T) / v2))
        = Real.exp (-(_root_.GD.N0155.d006324 v1 v2 u * T)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [_root_.GD.N0155.d006324]
    field_simp
    ring
  unfold _root_.GD.N0155.d006317 _root_.GD.N0155.d006305 _root_.GD.N0155.d006293 _root_.GD.N0155.d006326
  rw [hratio, hsum, ← hexp]
  field_simp <;> ring


lemma d006332 {v1 v2 u T : ℝ} (h1 : 0 < v1) (h2 : 0 < v2)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hT : 0 < T) :
    _root_.GD.N0155.d006318 v1 v2 (_root_.GD.N0155.d006305 (u, T)) * T =
      _root_.GD.N0155.d006326 v1 v2 * (_root_.GD.N0155.d006193 (1 - u) ^ 2 * (u ^ 4 * (1 - u) ^ 4) *
        (15 * (v1 + v2) ^ 2 * T ^ 7 - 21 * (v1 + v2) * T ^ 8
          + (49 / 4) * T ^ 9)) *
        Real.exp (-(_root_.GD.N0155.d006324 v1 v2 u * T)) := by
  have hT0 : T ≠ 0 := hT.ne'
  have hv1 : v1 ≠ 0 := h1.ne'
  have hv2 : v2 ≠ 0 := h2.ne'
  have h11T : (11 : ℝ) * ((1 - u) * T) + 11 * (u * T) ≠ 0 := by
    rw [show (11 : ℝ) * ((1 - u) * T) + 11 * (u * T) = 11 * T by ring]
    exact mul_ne_zero (by norm_num) hT0
  have hsum : u * T + (1 - u) * T = T := by ring
  have hratio : (11 : ℝ) * ((1 - u) * T) /
      (11 * ((1 - u) * T) + 11 * (u * T)) = 1 - u := by
    rw [show (11 : ℝ) * ((1 - u) * T) + 11 * (u * T) = 11 * T by ring]
    field_simp
  have hexp :
      Real.exp (-(5 * (u * T) / v1)) * Real.exp (-(5 * ((1 - u) * T) / v2))
        = Real.exp (-(_root_.GD.N0155.d006324 v1 v2 u * T)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [_root_.GD.N0155.d006324]
    field_simp
    ring
  unfold _root_.GD.N0155.d006318 _root_.GD.N0155.d006305 _root_.GD.N0155.d006293 _root_.GD.N0155.d006326
  rw [hratio, hsum, ← hexp]
  field_simp <;> ring




@[fun_prop]
lemma d006333 (v1 v2 : ℝ) :
    Measurable (fun p : ℝ × ℝ => _root_.GD.N0155.d006317 v1 v2 (_root_.GD.N0155.d006305 p) * p.2) := by
  unfold _root_.GD.N0155.d006317 _root_.GD.N0155.d006305 _root_.GD.N0155.d006293 _root_.GD.N0155.d006193 _root_.GD.N0155.d006267
  fun_prop

@[fun_prop]
lemma d006334 (v1 v2 : ℝ) :
    Measurable (fun p : ℝ × ℝ => _root_.GD.N0155.d006318 v1 v2 (_root_.GD.N0155.d006305 p) * p.2) := by
  unfold _root_.GD.N0155.d006318 _root_.GD.N0155.d006305 _root_.GD.N0155.d006293 _root_.GD.N0155.d006193
  fun_prop


lemma d006335 {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |_root_.GD.N0155.d006193 (1 - u)| ≤ 1 := by
  obtain ⟨hu0, hu1⟩ := hu
  have h1u_nn : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have h1u_le : 1 - u ≤ 1 := by linarith
  have hu_nn : 0 ≤ u := hu0
  have hu_le : u ≤ 1 := hu1

  unfold _root_.GD.N0155.d006193
  have h_1u_abs : |1 - u| ≤ 1 := by
    rw [abs_of_nonneg h1u_nn]; exact h1u_le
  have h_neg_abs : |(1 - u) - (1 / 2)| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have h_u_abs : |1 - (1 - u)| ≤ 1 := by
    rw [show (1 : ℝ) - (1 - u) = u by ring, abs_of_nonneg hu_nn]; exact hu_le
  have := mul_le_mul (mul_le_mul h_1u_abs h_u_abs (abs_nonneg _) (by norm_num))
                     h_neg_abs (abs_nonneg _) (by norm_num)
  calc |(1 - u) * (1 - (1 - u)) * ((1 - u) - 1 / 2)|
      = |1 - u| * |1 - (1 - u)| * |(1 - u) - 1 / 2| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 := by simpa using this


lemma d006336 {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    u ^ k ≤ 1 :=
  pow_le_one₀ hu.1 hu.2


noncomputable def d006337 (v1 v2 T : ℝ) : ℝ :=
  |_root_.GD.N0155.d006326 v1 v2| * (1 + |_root_.GD.N0155.d006267 (v2 / v1)|) *
    (3 * |v1 + v2| * (T ^ 8 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T))
      + (7 / 2) * (T ^ 9 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T)))


noncomputable def d006338 (v1 v2 T : ℝ) : ℝ :=
  |_root_.GD.N0155.d006326 v1 v2| *
    (15 * |v1 + v2| ^ 2 * (T ^ 7 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T))
      + 21 * |v1 + v2| * (T ^ 8 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T))
      + (49 / 4) * (T ^ 9 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T)))


lemma d006339 {v1 v2 u T : ℝ} (h1 : 0 < v1) (h2 : 0 < v2)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hT : 0 < T) :
    ‖_root_.GD.N0155.d006317 v1 v2 (_root_.GD.N0155.d006305 (u, T)) * T‖ ≤ _root_.GD.N0155.d006337 v1 v2 T := by
  have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  rw [_root_.GD.N0155.d006331 h1 h2 hu hT, Real.norm_eq_abs]
  set c0 := _root_.GD.N0155.d006325 v1 v2 with hc0_def
  set c := _root_.GD.N0155.d006324 v1 v2 u with hc_def
  have hc0_le_c : c0 ≤ c := _root_.GD.N0155.d006328 h1 h2 huIcc
  have hT_nn : 0 ≤ T := hT.le
  have hexp_pos_c : 0 < Real.exp (-(c * T)) := Real.exp_pos _
  have hexp_pos_c0 : 0 < Real.exp (-(c0 * T)) := Real.exp_pos _
  have hexp_bound : Real.exp (-(c * T)) ≤ Real.exp (-(c0 * T)) := by
    apply Real.exp_le_exp.mpr
    have : c0 * T ≤ c * T := mul_le_mul_of_nonneg_right hc0_le_c hT_nn
    linarith
  have h1u_nn : 0 ≤ 1 - u := sub_nonneg.mpr hu.2.le
  have hu_nn : 0 ≤ u := hu.1.le
  have hu4_le : u ^ 4 ≤ 1 := pow_le_one₀ hu_nn hu.2.le
  have h1u4_le : (1 - u) ^ 4 ≤ 1 := pow_le_one₀ h1u_nn (by linarith [hu.1])
  have hu4_nn : 0 ≤ u ^ 4 := by positivity
  have h1u4_nn : 0 ≤ (1 - u) ^ 4 := by positivity
  have hpsi_bound : |_root_.GD.N0155.d006193 (1 - u)| ≤ 1 := _root_.GD.N0155.d006335 huIcc
  have hdiff_bound : |1 - u - _root_.GD.N0155.d006267 (v2 / v1)| ≤ 1 + |_root_.GD.N0155.d006267 (v2 / v1)| := by
    calc |1 - u - _root_.GD.N0155.d006267 (v2 / v1)|
        ≤ |1 - u| + |_root_.GD.N0155.d006267 (v2 / v1)| := abs_sub _ _
      _ ≤ 1 + |_root_.GD.N0155.d006267 (v2 / v1)| := by
          rw [abs_of_nonneg h1u_nn]
          gcongr
          linarith [hu.1]
  have hT8_nn : 0 ≤ T ^ 8 := by positivity
  have hT9_nn : 0 ≤ T ^ 9 := by positivity

  have hA_bound : |_root_.GD.N0155.d006193 (1 - u) * (1 - u - _root_.GD.N0155.d006267 (v2 / v1)) *
                    (u ^ 4 * (1 - u) ^ 4)| ≤ 1 + |_root_.GD.N0155.d006267 (v2 / v1)| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hu4_nn, abs_of_nonneg h1u4_nn]
    have h1 : |_root_.GD.N0155.d006193 (1 - u)| * |1 - u - _root_.GD.N0155.d006267 (v2 / v1)| ≤ 1 * (1 + |_root_.GD.N0155.d006267 (v2 / v1)|) :=
      mul_le_mul hpsi_bound hdiff_bound (abs_nonneg _) (by norm_num)
    have h2 : u ^ 4 * (1 - u) ^ 4 ≤ 1 * 1 :=
      mul_le_mul hu4_le h1u4_le h1u4_nn (by norm_num)
    have h3 := mul_le_mul h1 h2 (by positivity)
      (mul_nonneg (by norm_num) (by positivity : (0 : ℝ) ≤ 1 + |_root_.GD.N0155.d006267 (v2 / v1)|))
    linarith

  have hB_bound :
      |3 * (v1 + v2) * T ^ 8 - (7 / 2) * T ^ 9|
        ≤ 3 * |v1 + v2| * T ^ 8 + (7 / 2) * T ^ 9 := by
    calc |3 * (v1 + v2) * T ^ 8 - (7 / 2) * T ^ 9|
        ≤ |3 * (v1 + v2) * T ^ 8| + |(7 / 2) * T ^ 9| := abs_sub _ _
      _ = 3 * |v1 + v2| * T ^ 8 + (7 / 2) * T ^ 9 := by
          rw [show (3 : ℝ) * (v1 + v2) * T ^ 8 = 3 * ((v1 + v2) * T ^ 8) by ring,
              show (7 / 2 : ℝ) * T ^ 9 = (7/2) * T ^ 9 from rfl,
              abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
              abs_mul, abs_of_nonneg hT8_nn,
              abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7/2),
              abs_of_nonneg hT9_nn]
          ring

  have hpref_nn : 0 ≤ |_root_.GD.N0155.d006326 v1 v2| := abs_nonneg _
  have hA_nn : 0 ≤ |_root_.GD.N0155.d006193 (1 - u) * (1 - u - _root_.GD.N0155.d006267 (v2 / v1)) *
                    (u ^ 4 * (1 - u) ^ 4)| := abs_nonneg _
  have hB_nn : 0 ≤ |3 * (v1 + v2) * T ^ 8 - (7 / 2) * T ^ 9| := abs_nonneg _
  have h_1_eta_nn : 0 ≤ 1 + |_root_.GD.N0155.d006267 (v2 / v1)| := by positivity
  have hpoly_nn : 0 ≤ 3 * |v1 + v2| * T ^ 8 + (7 / 2) * T ^ 9 := by positivity

  set A := _root_.GD.N0155.d006193 (1 - u) * (1 - u - _root_.GD.N0155.d006267 (v2 / v1)) * (u ^ 4 * (1 - u) ^ 4) with hA_def
  set B := 3 * (v1 + v2) * T ^ 8 - (7 / 2) * T ^ 9 with hB_def
  have h_abs_eq :
      |_root_.GD.N0155.d006326 v1 v2 * (A * B) * Real.exp (-(c * T))|
        = |_root_.GD.N0155.d006326 v1 v2| * (|A| * |B|) * Real.exp (-(c * T)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hexp_pos_c]
  rw [h_abs_eq]

  have hAB_bound : |A| * |B|
      ≤ (1 + |_root_.GD.N0155.d006267 (v2 / v1)|) * (3 * |v1 + v2| * T ^ 8 + (7 / 2) * T ^ 9) :=
    mul_le_mul hA_bound hB_bound hB_nn h_1_eta_nn
  have step1 : |_root_.GD.N0155.d006326 v1 v2| * (|A| * |B|) * Real.exp (-(c * T))
      ≤ |_root_.GD.N0155.d006326 v1 v2| * ((1 + |_root_.GD.N0155.d006267 (v2 / v1)|) *
          (3 * |v1 + v2| * T ^ 8 + (7 / 2) * T ^ 9)) * Real.exp (-(c0 * T)) := by
    have h_left_nn : 0 ≤ |_root_.GD.N0155.d006326 v1 v2| * (|A| * |B|) :=
      mul_nonneg hpref_nn (mul_nonneg hA_nn hB_nn)
    have h_middle_nn' : 0 ≤ |_root_.GD.N0155.d006326 v1 v2| * ((1 + |_root_.GD.N0155.d006267 (v2 / v1)|) *
        (3 * |v1 + v2| * T ^ 8 + (7 / 2) * T ^ 9)) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hAB_bound hpref_nn)
      hexp_bound hexp_pos_c.le h_middle_nn'
  refine step1.trans ?_
  unfold _root_.GD.N0155.d006337
  rw [← hc0_def]
  ring_nf
  rfl


lemma d006340 {v1 v2 u T : ℝ} (h1 : 0 < v1) (h2 : 0 < v2)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hT : 0 < T) :
    ‖_root_.GD.N0155.d006318 v1 v2 (_root_.GD.N0155.d006305 (u, T)) * T‖ ≤ _root_.GD.N0155.d006338 v1 v2 T := by
  have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  rw [_root_.GD.N0155.d006332 h1 h2 hu hT, Real.norm_eq_abs]
  set c0 := _root_.GD.N0155.d006325 v1 v2 with hc0_def
  set c := _root_.GD.N0155.d006324 v1 v2 u with hc_def
  have hc0_le_c : c0 ≤ c := _root_.GD.N0155.d006328 h1 h2 huIcc
  have hT_nn : 0 ≤ T := hT.le
  have hexp_pos_c : 0 < Real.exp (-(c * T)) := Real.exp_pos _
  have hexp_bound : Real.exp (-(c * T)) ≤ Real.exp (-(c0 * T)) := by
    apply Real.exp_le_exp.mpr
    have : c0 * T ≤ c * T := mul_le_mul_of_nonneg_right hc0_le_c hT_nn
    linarith
  have hpsi_bound : |_root_.GD.N0155.d006193 (1 - u)| ≤ 1 := _root_.GD.N0155.d006335 huIcc
  have hpsi_sq_bound : |_root_.GD.N0155.d006193 (1 - u) ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hpsi_bound
  have h1u_nn : 0 ≤ 1 - u := sub_nonneg.mpr hu.2.le
  have hu_nn : 0 ≤ u := hu.1.le
  have hu4_nn : 0 ≤ u ^ 4 := by positivity
  have h1u4_nn : 0 ≤ (1 - u) ^ 4 := by positivity
  have hu4_le : u ^ 4 ≤ 1 := pow_le_one₀ hu_nn hu.2.le
  have h1u4_le : (1 - u) ^ 4 ≤ 1 := pow_le_one₀ h1u_nn (by linarith [hu.1])
  have hT7_nn : 0 ≤ T ^ 7 := by positivity
  have hT8_nn : 0 ≤ T ^ 8 := by positivity
  have hT9_nn : 0 ≤ T ^ 9 := by positivity

  have hA_bound :
      |_root_.GD.N0155.d006193 (1 - u) ^ 2 * (u ^ 4 * (1 - u) ^ 4)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu4_nn, abs_of_nonneg h1u4_nn]
    have h1 : |_root_.GD.N0155.d006193 (1 - u) ^ 2| * (u ^ 4 * (1 - u) ^ 4) ≤ 1 * (1 * 1) := by
      refine mul_le_mul hpsi_sq_bound ?_ (by positivity) (by norm_num)
      exact mul_le_mul hu4_le h1u4_le h1u4_nn (by norm_num)
    linarith

  have hB_bound :
      |15 * (v1 + v2) ^ 2 * T ^ 7 - 21 * (v1 + v2) * T ^ 8 + (49 / 4) * T ^ 9|
        ≤ 15 * |v1 + v2| ^ 2 * T ^ 7 + 21 * |v1 + v2| * T ^ 8 + (49 / 4) * T ^ 9 := by
    have step1 :
        |15 * (v1 + v2) ^ 2 * T ^ 7 - 21 * (v1 + v2) * T ^ 8 + (49 / 4) * T ^ 9|
          ≤ |15 * (v1 + v2) ^ 2 * T ^ 7 - 21 * (v1 + v2) * T ^ 8|
            + |(49 / 4) * T ^ 9| := abs_add_le _ _
    have step2 :
        |15 * (v1 + v2) ^ 2 * T ^ 7 - 21 * (v1 + v2) * T ^ 8|
          ≤ |15 * (v1 + v2) ^ 2 * T ^ 7| + |21 * (v1 + v2) * T ^ 8| := abs_sub _ _
    have e1 : |15 * (v1 + v2) ^ 2 * T ^ 7| = 15 * |v1 + v2| ^ 2 * T ^ 7 := by
      rw [show (15 : ℝ) * (v1 + v2) ^ 2 * T ^ 7 = 15 * ((v1 + v2) ^ 2 * T ^ 7) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 15),
          abs_mul, abs_pow, abs_of_nonneg hT7_nn]
      ring
    have e2 : |21 * (v1 + v2) * T ^ 8| = 21 * |v1 + v2| * T ^ 8 := by
      rw [show (21 : ℝ) * (v1 + v2) * T ^ 8 = 21 * ((v1 + v2) * T ^ 8) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 21),
          abs_mul, abs_of_nonneg hT8_nn]
      ring
    have e3 : |(49 / 4) * T ^ 9| = (49 / 4) * T ^ 9 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 49/4), abs_of_nonneg hT9_nn]
    linarith

  have hpref_nn : 0 ≤ |_root_.GD.N0155.d006326 v1 v2| := abs_nonneg _
  have hA_nn : 0 ≤ |_root_.GD.N0155.d006193 (1 - u) ^ 2 * (u ^ 4 * (1 - u) ^ 4)| := abs_nonneg _
  have hB_nn : 0 ≤ |15 * (v1 + v2) ^ 2 * T ^ 7 - 21 * (v1 + v2) * T ^ 8
                      + (49 / 4) * T ^ 9| := abs_nonneg _
  have hpoly_nn : 0 ≤ 15 * |v1 + v2| ^ 2 * T ^ 7 + 21 * |v1 + v2| * T ^ 8
                        + (49 / 4) * T ^ 9 := by positivity
  set A := _root_.GD.N0155.d006193 (1 - u) ^ 2 * (u ^ 4 * (1 - u) ^ 4) with hA_def
  set B := 15 * (v1 + v2) ^ 2 * T ^ 7 - 21 * (v1 + v2) * T ^ 8 + (49 / 4) * T ^ 9 with hB_def
  have h_abs_eq :
      |_root_.GD.N0155.d006326 v1 v2 * (A * B) * Real.exp (-(c * T))|
        = |_root_.GD.N0155.d006326 v1 v2| * (|A| * |B|) * Real.exp (-(c * T)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hexp_pos_c]
  rw [h_abs_eq]
  have hAB_bound : |A| * |B|
      ≤ 1 * (15 * |v1 + v2| ^ 2 * T ^ 7 + 21 * |v1 + v2| * T ^ 8 + (49 / 4) * T ^ 9) :=
    mul_le_mul hA_bound hB_bound hB_nn (by norm_num)
  have step1 : |_root_.GD.N0155.d006326 v1 v2| * (|A| * |B|) * Real.exp (-(c * T))
      ≤ |_root_.GD.N0155.d006326 v1 v2| * (1 * (15 * |v1 + v2| ^ 2 * T ^ 7
          + 21 * |v1 + v2| * T ^ 8 + (49 / 4) * T ^ 9)) * Real.exp (-(c0 * T)) := by
    have h_middle_nn' : 0 ≤ |_root_.GD.N0155.d006326 v1 v2| * (1 * (15 * |v1 + v2| ^ 2 * T ^ 7
        + 21 * |v1 + v2| * T ^ 8 + (49 / 4) * T ^ 9)) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hAB_bound hpref_nn)
      hexp_bound hexp_pos_c.le h_middle_nn'
  refine step1.trans ?_
  unfold _root_.GD.N0155.d006338
  rw [← hc0_def]
  ring_nf
  rfl


lemma d006341 {v1 v2 : ℝ} (h1 : 0 < v1) (h2 : 0 < v2) :
    IntegrableOn (_root_.GD.N0155.d006337 v1 v2) (Set.Ioi 0) volume := by
  have hc : 0 < _root_.GD.N0155.d006325 v1 v2 := _root_.GD.N0155.d006327 h1 h2
  have h8 := _root_.GD.N0155.d006329 8 hc
  have h9 := _root_.GD.N0155.d006329 9 hc
  have hCombined :
      IntegrableOn (fun T : ℝ =>
        3 * |v1 + v2| * (T ^ 8 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T))
        + (7 / 2) * (T ^ 9 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T)))
        (Set.Ioi 0) volume := by
    refine (h8.const_mul (3 * |v1 + v2|)).add (h9.const_mul (7 / 2))
  have := hCombined.const_mul (|_root_.GD.N0155.d006326 v1 v2| * (1 + |_root_.GD.N0155.d006267 (v2 / v1)|))
  refine this.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
  intro T _
  simp only [_root_.GD.N0155.d006337] <;> ring


lemma d006342 {v1 v2 : ℝ} (h1 : 0 < v1) (h2 : 0 < v2) :
    IntegrableOn (_root_.GD.N0155.d006338 v1 v2) (Set.Ioi 0) volume := by
  have hc : 0 < _root_.GD.N0155.d006325 v1 v2 := _root_.GD.N0155.d006327 h1 h2
  have h7 := _root_.GD.N0155.d006329 7 hc
  have h8 := _root_.GD.N0155.d006329 8 hc
  have h9 := _root_.GD.N0155.d006329 9 hc
  have hCombined :
      IntegrableOn (fun T : ℝ =>
        15 * |v1 + v2| ^ 2 * (T ^ 7 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T))
        + 21 * |v1 + v2| * (T ^ 8 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T))
        + (49 / 4) * (T ^ 9 * Real.exp (-_root_.GD.N0155.d006325 v1 v2 * T)))
        (Set.Ioi 0) volume := by
    refine ((h7.const_mul (15 * |v1 + v2| ^ 2)).add
      (h8.const_mul (21 * |v1 + v2|))).add (h9.const_mul (49 / 4))
  have := hCombined.const_mul (|_root_.GD.N0155.d006326 v1 v2|)
  refine this.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
  intro T _
  simp only [_root_.GD.N0155.d006338] <;> ring


theorem d006343 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2) :
    IntegrableOn (fun p : ℝ × ℝ => _root_.GD.N0155.d006317 v1 v2 (_root_.GD.N0155.d006305 p) * p.2)
      _root_.GD.N0155.d006307 volume := by
  have hM_Ioi : IntegrableOn (_root_.GD.N0155.d006337 v1 v2) (Set.Ioi 0) volume :=
    _root_.GD.N0155.d006341 h1 h2
  have hM : IntegrableOn (fun p : ℝ × ℝ => _root_.GD.N0155.d006337 v1 v2 p.2) _root_.GD.N0155.d006307 volume :=
    _root_.GD.N0155.d006330 hM_Ioi
  have hSpolar : MeasurableSet _root_.GD.N0155.d006307 :=
    measurableSet_Ioo.prod measurableSet_Ioi
  refine hM.mono' (_root_.GD.N0155.d006333 v1 v2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hSpolar).mpr (Filter.Eventually.of_forall ?_)
  rintro ⟨u, T⟩ hp
  exact _root_.GD.N0155.d006339 h1 h2 hp.1 hp.2


theorem d006344 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2) :
    IntegrableOn (fun p : ℝ × ℝ => _root_.GD.N0155.d006318 v1 v2 (_root_.GD.N0155.d006305 p) * p.2)
      _root_.GD.N0155.d006307 volume := by
  have hM_Ioi : IntegrableOn (_root_.GD.N0155.d006338 v1 v2) (Set.Ioi 0) volume :=
    _root_.GD.N0155.d006342 h1 h2
  have hM : IntegrableOn (fun p : ℝ × ℝ => _root_.GD.N0155.d006338 v1 v2 p.2) _root_.GD.N0155.d006307 volume :=
    _root_.GD.N0155.d006330 hM_Ioi
  have hSpolar : MeasurableSet _root_.GD.N0155.d006307 :=
    measurableSet_Ioo.prod measurableSet_Ioi
  refine hM.mono' (_root_.GD.N0155.d006334 v1 v2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hSpolar).mpr (Filter.Eventually.of_forall ?_)
  rintro ⟨u, T⟩ hp
  exact _root_.GD.N0155.d006340 h1 h2 hp.1 hp.2





theorem d006345 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2) :
    _root_.GD.N0155.d006297 v1 v2 = _root_.GD.N0155.d006299 v1 v2 ∧ _root_.GD.N0155.d006298 v1 v2 = _root_.GD.N0155.d006300 v1 v2 :=
  _root_.GD.N0155.d006323
    (_root_.GD.N0155.d006343 v1 v2 h1 h2)
    (_root_.GD.N0155.d006344 v1 v2 h1 h2)

end GD.N0155
