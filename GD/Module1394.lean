import GD.Module1391














set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0198
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0163 _root_.GD.N0178 _root_.GD.N0179
open _root_.GD.N0165 _root_.GD.N0169
open _root_.GD.N0174 _root_.GD.N0168

def d022440 (eta a b : ℝ) : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  (volume.restrict (Ioc eta (1 - eta))).prod (volume.restrict (Ioc a b))

local instance d022441 (eta a b : ℝ) : SFinite (_root_.GD.N0198.d022440 eta a b) := by
  unfold _root_.GD.N0198.d022440
  infer_instance


def d022442 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (r : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0178.d007131 (Real.exp (-r)) p.1 (p.2 / Real.exp (-r)) / Real.exp (-r) *
      (_root_.GD.N0163.d022211 g (p.1, p.2 / Real.exp (-r)) - Real.exp (-r)) ^ 2 +
    _root_.GD.N0178.d007131 (1 - Real.exp (-r)) p.1 (p.2 / Real.exp (-r)) / Real.exp (-r) *
      (_root_.GD.N0163.d022211 g (p.1, p.2 / Real.exp (-r)) - (1 - Real.exp (-r))) ^ 2

def d022443 (eta a b A T : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) : ℝ :=
  1 / (2 * T) * ∫ r in A..(A + T), ∫ p, _root_.GD.N0198.d022442 g r p ∂_root_.GD.N0198.d022440 eta a b

theorem d022444 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    (r : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0198.d022442 g r p = _root_.GD.N0174.d022396 g r (p.1, p.2 / Real.exp (-r)) / Real.exp (-r) := by
  unfold _root_.GD.N0198.d022442 _root_.GD.N0174.d022396
  ring

theorem d022445 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g) :
    Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0198.d022442 g z.1 z.2) := by
  have hv : Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0163.d022211 g (z.2.1, z.2.2 / Real.exp (-z.1))) :=
    (_root_.GD.N0163.d022213 g hg).comp (by fun_prop)
  unfold _root_.GD.N0198.d022442 _root_.GD.N0178.d007131 _root_.GD.N0178.d007130 _root_.GD.N0178.d007129
  fun_prop

private theorem d022446 {t u s : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 < s) :
    ContinuousAt (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0178.d007131 z.1 z.2.1 z.2.2) (t, (u, s)) := by
  have htne : t ≠ 0 := ht.ne'
  have honepos : 0 < 1 - t := sub_pos.mpr ht1
  have hone : 1 - t ≠ 0 := honepos.ne'
  have hD := _root_.GD.N0178.d007138 ht ht1 hu hu1 hs
  have hseven := _root_.GD.N0178.d007134 hD
  unfold _root_.GD.N0178.d007131
  apply ContinuousAt.div
  · fun_prop
  · unfold _root_.GD.N0178.d007130 _root_.GD.N0178.d007129
    fun_prop
  · exact (show 0 < t ^ 2 * (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t u s) by
      positivity).ne'

private theorem d022447 {A B eta a b : ℝ}
    (heta : 0 < eta) (ha : 0 < a) (t : ℝ → ℝ) (ht : Continuous t)
    (ht01 : ∀ r ∈ Icc A B, t r ∈ Ioo (0 : ℝ) 1)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0178.d007131 (t z.1) z.2.1 (z.2.2 / Real.exp (-z.1)) / Real.exp (-z.1) *
        (_root_.GD.N0163.d022211 g (z.2.1, z.2.2 / Real.exp (-z.1)) - t z.1) ^ 2)
      ((volume.restrict (Ioc A B)).prod (_root_.GD.N0198.d022440 eta a b)) := by
  let K : Set (ℝ × _root_.GD.N0232.N0720.N1436.d013217) := Icc A B ×ˢ (Icc eta (1 - eta) ×ˢ Icc a b)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcoordinate : Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      z.2.2 / Real.exp (-z.1)) :=
    continuous_snd.snd.div (by fun_prop) (fun z => (Real.exp_pos (-z.1)).ne')
  have hmap : Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      (t z.1, (z.2.1, z.2.2 / Real.exp (-z.1)))) := by
    exact (ht.comp continuous_fst).prodMk (continuous_snd.fst.prodMk hcoordinate)
  have hc : ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0178.d007131 (t z.1) z.2.1 (z.2.2 / Real.exp (-z.1)) / Real.exp (-z.1)) K := by
    intro z hz
    have hf := ht01 z.1 hz.1
    have hu0 : 0 ≤ z.2.1 := (heta.trans_le hz.2.1.1).le
    have hu1 : z.2.1 ≤ 1 := by linarith [hz.2.1.2]
    have hs : 0 < z.2.2 / Real.exp (-z.1) :=
      div_pos (ha.trans_le hz.2.2.1) (Real.exp_pos _)
    have hkernel : ContinuousAt
        (fun w : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0178.d007131 w.1 w.2.1 w.2.2)
        (t z.1, (z.2.1, z.2.2 / Real.exp (-z.1))) :=
      _root_.GD.N0198.d022446 hf.1 hf.2 hu0 hu1 hs
    have hk : ContinuousAt (fun w : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
        _root_.GD.N0178.d007131 (t w.1) w.2.1 (w.2.2 / Real.exp (-w.1))) z :=
      hkernel.comp (f := fun w : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
        (t w.1, (w.2.1, w.2.2 / Real.exp (-w.1)))) (x := z) hmap.continuousAt
    exact (hk.div (by fun_prop) (Real.exp_pos _).ne').continuousWithinAt
  have hi : IntegrableOn (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0178.d007131 (t z.1) z.2.1 (z.2.2 / Real.exp (-z.1)) / Real.exp (-z.1)) K volume :=
    hc.integrableOn_compact hK
  have hv : Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0163.d022211 g (z.2.1, z.2.2 / Real.exp (-z.1))) :=
    (_root_.GD.N0163.d022213 g hg).comp (by fun_prop)
  have hsq := Integrable.mul_bdd hi
    (show Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      (_root_.GD.N0163.d022211 g (z.2.1, z.2.2 / Real.exp (-z.1)) - t z.1) ^ 2) by
        fun_prop).aestronglyMeasurable (c := (1 : ℝ)) (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hv01 := _root_.GD.N0163.d022214 g h01 (z.2.1, z.2.2 / Real.exp (-z.1))
      have hf := ht01 z.1 hz.1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hleft : 0 ≤ 1 - (_root_.GD.N0163.d022211 g (z.2.1, z.2.2 / Real.exp (-z.1)) - t z.1) := by
        linarith [hv01.2, hf.1]
      have hright : 0 ≤ 1 + (_root_.GD.N0163.d022211 g (z.2.1, z.2.2 / Real.exp (-z.1)) - t z.1) := by
        linarith [hv01.1, hf.2]
      nlinarith [mul_nonneg hleft hright])
  have hopen := IntegrableOn.mono_set hsq (show Ioc A B ×ˢ (Ioc eta (1 - eta) ×ˢ Ioc a b) ⊆ K from
    fun z hz => ⟨⟨hz.1.1.le, hz.1.2⟩,
      ⟨⟨hz.2.1.1.le, hz.2.1.2⟩, ⟨hz.2.2.1.le, hz.2.2.2⟩⟩⟩)
  simpa only [IntegrableOn, _root_.GD.N0198.d022440, Measure.prod_restrict,
    MeasureTheory.Measure.volume_eq_prod] using hopen


theorem d022448 {A B eta a b : ℝ}
    (hA : 0 < A) (heta : 0 < eta) (ha : 0 < a)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0198.d022442 g z.1 z.2)
      ((volume.restrict (Ioc A B)).prod (_root_.GD.N0198.d022440 eta a b)) := by
  have h0 := _root_.GD.N0198.d022447 (A := A) (B := B) (b := b) heta ha
    (fun r => Real.exp (-r)) (by fun_prop) (by
      intro r hr
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith [hr.1])⟩) g hg h01
  have h1 := _root_.GD.N0198.d022447 (A := A) (B := B) (b := b) heta ha
    (fun r => 1 - Real.exp (-r)) (by fun_prop) (by
      intro r hr
      have he : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hr.1])
      constructor <;> linarith [Real.exp_pos (-r)]) g hg h01
  exact h0.add h1

private theorem d022449 (A B eta a b : ℝ) :
    ∀ᵐ z : ℝ × _root_.GD.N0232.N0720.N1436.d013217
      ∂((volume.restrict (Ioc A B)).prod (_root_.GD.N0198.d022440 eta a b)),
      z ∈ Ioc A B ×ˢ (Ioc eta (1 - eta) ×ˢ Ioc a b) := by
  simpa only [_root_.GD.N0198.d022440, Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod] using
    (ae_restrict_mem (measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)) :
      ∀ᵐ z : ℝ × _root_.GD.N0232.N0720.N1436.d013217
        ∂(volume.restrict (Ioc A B ×ˢ (Ioc eta (1 - eta) ×ˢ Ioc a b))),
        z ∈ Ioc A B ×ˢ (Ioc eta (1 - eta) ×ˢ Ioc a b))

private theorem d022450 {A B eta a b : ℝ}
    (hAB : A ≤ B) (hhalf : eta ≤ 1 / 2) (hab : a ≤ b)
    {F : ℝ × _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hF : Integrable F ((volume.restrict (Ioc A B)).prod (_root_.GD.N0198.d022440 eta a b))) :
    (∫ r in A..B, ∫ p, F (r, p) ∂_root_.GD.N0198.d022440 eta a b) =
      ∫ u in eta..(1 - eta), ∫ x in a..b, ∫ r in A..B, F (r, (u, x)) := by
  have hU : eta ≤ 1 - eta := by linarith
  have hswap := MeasureTheory.integral_integral_swap (f := fun r p => F (r, p)) hF
  have hright := hF.integral_prod_right
  calc
    _ = ∫ p, (∫ r in A..B, F (r, p)) ∂_root_.GD.N0198.d022440 eta a b := by
      simpa only [intervalIntegral.integral_of_le hAB] using hswap
    _ = _ := by
      have h := MeasureTheory.integral_prod (fun p => ∫ r, F (r, p) ∂volume.restrict (Ioc A B)) hright
      simpa only [_root_.GD.N0198.d022440, intervalIntegral.integral_of_le hAB,
        intervalIntegral.integral_of_le hU, intervalIntegral.integral_of_le hab] using h

theorem d022451 {A B eta a b : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (heta : 0 < eta) (hhalf : eta ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ r in A..B, ∫ p, _root_.GD.N0198.d022442 g r p ∂_root_.GD.N0198.d022440 eta a b) =
      ∫ u in eta..(1 - eta), ∫ x in a..b, ∫ r in A..B, _root_.GD.N0198.d022442 g r (u, x) :=
  _root_.GD.N0198.d022450 hAB hhalf hab (_root_.GD.N0198.d022448 hA heta ha g hg h01)


theorem d022452 {r eta a b : ℝ} (hr : 0 < r)
    (heta : 0 < eta) (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ u in eta..(1 - eta), ∫ x in a..b, _root_.GD.N0198.d022442 g r (u, x)) ≤
      ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  let c := Real.exp (-r)
  have hc : 0 < c := Real.exp_pos _
  have hU : eta ≤ 1 - eta := by linarith
  have hX : a / c ≤ b / c := div_le_div_of_nonneg_right hab hc.le
  have hi : IntegrableOn (_root_.GD.N0174.d022396 g r) (_root_.GD.N0169.d022354 eta a b c) volume :=
    (_root_.GD.N0169.d022361 heta ha hc (_root_.GD.N0174.d022394 r hr) g hg h01).add
      (_root_.GD.N0169.d022361 heta ha hc (_root_.GD.N0174.d022395 r hr) g hg h01)
  have hprod := MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (_root_.GD.N0174.d022396 g r) hi
  have hs (u : ℝ) : (∫ x in a..b, _root_.GD.N0198.d022442 g r (u, x)) =
      ∫ s in (a / c)..(b / c), _root_.GD.N0174.d022396 g r (u, s) := by
    have h := intervalIntegral.inv_smul_integral_comp_div
      (a := a) (b := b) (fun s => _root_.GD.N0174.d022396 g r (u, s)) c
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul] at h
    calc
      _ = ∫ x in a..b, c⁻¹ * _root_.GD.N0174.d022396 g r (u, x / c) := by
        apply intervalIntegral.integral_congr
        intro x _
        change _root_.GD.N0198.d022442 g r (u, x) = c⁻¹ * _root_.GD.N0174.d022396 g r (u, x / c)
        rw [_root_.GD.N0198.d022444]
        dsimp [c]
        ring
      _ = _ := h
  calc
    _ = ∫ p in _root_.GD.N0169.d022354 eta a b c, _root_.GD.N0174.d022396 g r p := by
      calc
        _ = ∫ u in eta..(1 - eta), ∫ s in (a / c)..(b / c), _root_.GD.N0174.d022396 g r (u, s) :=
          intervalIntegral.integral_congr (fun u _ => hs u)
        _ = _ := by
          simpa only [_root_.GD.N0169.d022354, MeasureTheory.Measure.volume_eq_prod,
            intervalIntegral.integral_of_le hU,
            intervalIntegral.integral_of_le hX] using hprod.symm
    _ ≤ _ := by
      exact setIntegral_mono_set (_root_.GD.N0174.d022400 hr g hg h01)
        (by
          filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
          exact _root_.GD.N0174.d022399 hr g hp)
        (ae_of_all _ (fun p hp => _root_.GD.N0169.d022358 heta ha hc hp))


theorem d022453 {A T eta a b : ℝ}
    (hA : 0 < A) (hT : 0 < T) (heta : 0 < eta) (hhalf : eta ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0198.d022443 eta a b A T g ≤ _root_.GD.N0174.d022397 A T g := by
  have hAB : A ≤ A + T := by linarith
  have hU : eta ≤ 1 - eta := by linarith
  have hi := _root_.GD.N0198.d022448 (B := A + T) (b := b) hA heta ha g hg h01
  have ho := _root_.GD.N0174.d022409 hA hAB g hg h01
  unfold _root_.GD.N0198.d022443 _root_.GD.N0174.d022397
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [intervalIntegral.integral_of_le hAB]
  apply integral_mono_ae hi.integral_prod_left ho.1
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hi.prod_right_ae] with r hr hir
  have hprod := MeasureTheory.integral_prod (fun p => _root_.GD.N0198.d022442 g r p) hir
  have he : (∫ p, _root_.GD.N0198.d022442 g r p ∂_root_.GD.N0198.d022440 eta a b) =
      ∫ u in eta..(1 - eta), ∫ x in a..b, _root_.GD.N0198.d022442 g r (u, x) := by
    simpa only [_root_.GD.N0198.d022440, intervalIntegral.integral_of_le hU,
      intervalIntegral.integral_of_le hab] using hprod
  rw [he]
  exact _root_.GD.N0198.d022452 (hA.trans hr.1) heta hhalf ha hab g hg h01

theorem d022454 {A eta a : ℝ} (hA : 0 < A) (heta : 0 < eta) (ha : 0 < a) :
    0 < _root_.GD.N0165.d007234 (Real.exp (-A)) eta a := by
  have hd : Real.exp (-A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hb := _root_.GD.N0165.d007239 (Real.exp_pos (-A)) hd heta ha
  exact Real.rpow_pos_of_pos (by linarith : 0 < 1 + _root_.GD.N0165.d007233 (Real.exp (-A)) eta a) _


theorem d022455 {A eta a r u x : ℝ}
    (hA : 0 < A) (heta : 0 < eta) (ha : 0 < a) (hr : A ≤ r)
    (hu : eta ≤ u) (hu1 : u ≤ 1 - eta) (hx : a ≤ x) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) :
    _root_.GD.N0165.d007234 (Real.exp (-A)) eta a * _root_.GD.N0168.d022365 u x g r ≤ _root_.GD.N0198.d022442 g r (u, x) := by
  have hd : Real.exp (-A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have htd : Real.exp (-r) ≤ Real.exp (-A) := Real.exp_le_exp_of_le (by linarith)
  have hk0 := _root_.GD.N0165.d007243 (Real.exp_pos (-r)) htd hd heta ha hu hu1 hx
  have hk1 := _root_.GD.N0165.d007245 (Real.exp_pos (-r)) htd hd heta ha hu hu1 hx
  have h0 := mul_le_mul_of_nonneg_right hk0
    (sq_nonneg (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - Real.exp (-r)))
  have h1 := mul_le_mul_of_nonneg_right hk1
    (sq_nonneg (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - (1 - Real.exp (-r))))
  calc
    _ = (_root_.GD.N0165.d007234 (Real.exp (-A)) eta a * _root_.GD.N0179.d006018 u x) *
          (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - Real.exp (-r)) ^ 2 +
        (_root_.GD.N0165.d007234 (Real.exp (-A)) eta a * _root_.GD.N0179.d006018 (1 - u) x) *
          (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - (1 - Real.exp (-r))) ^ 2 := by
      unfold _root_.GD.N0168.d022365
      ring
    _ ≤ _root_.GD.N0178.d007131 (Real.exp (-r)) u (x / Real.exp (-r)) / Real.exp (-r) *
          (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - Real.exp (-r)) ^ 2 +
        _root_.GD.N0178.d007131 (1 - Real.exp (-r)) u (x / Real.exp (-r)) / Real.exp (-r) *
          (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - (1 - Real.exp (-r))) ^ 2 :=
      add_le_add h0 h1
    _ = _root_.GD.N0198.d022442 g r (u, x) := rfl

theorem d022456 {A B eta a b : ℝ}
    (hA : 0 < A) (heta : 0 < eta) (ha : 0 < a)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0168.d022365 z.2.1 z.2.2 g z.1)
      ((volume.restrict (Ioc A B)).prod (_root_.GD.N0198.d022440 eta a b)) := by
  have hv : Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0163.d022211 g (z.2.1, z.2.2 / Real.exp (-z.1))) :=
    (_root_.GD.N0163.d022213 g hg).comp (by fun_prop)
  have hm : Measurable (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0168.d022365 z.2.1 z.2.2 g z.1) := by
    unfold _root_.GD.N0168.d022365 _root_.GD.N0179.d006018
    fun_prop
  have hrho := _root_.GD.N0198.d022454 hA heta ha
  apply Integrable.mono' ((_root_.GD.N0198.d022448 hA heta ha g hg h01).div_const
    (_root_.GD.N0165.d007234 (Real.exp (-A)) eta a)) hm.aestronglyMeasurable
  filter_upwards [_root_.GD.N0198.d022449 A B eta a b] with z hz
  have hu : 0 < z.2.1 := heta.trans hz.2.1.1
  have hu1 : 0 < 1 - z.2.1 := by linarith [hz.2.1.2]
  have hx : 0 < z.2.2 := ha.trans hz.2.2.1
  have hk0 : 0 ≤ _root_.GD.N0179.d006018 z.2.1 z.2.2 := by unfold _root_.GD.N0179.d006018; positivity
  have hk1 : 0 ≤ _root_.GD.N0179.d006018 (1 - z.2.1) z.2.2 := by unfold _root_.GD.N0179.d006018; positivity
  have hn : 0 ≤ _root_.GD.N0168.d022365 z.2.1 z.2.2 g z.1 :=
    add_nonneg (mul_nonneg hk0 (sq_nonneg _)) (mul_nonneg hk1 (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  apply (le_div_iff₀ hrho).mpr
  have hd := _root_.GD.N0198.d022455 hA heta ha hz.1.1.le hz.2.1.1.le hz.2.1.2 hz.2.2.1.le g
  nlinarith [hd]


theorem d022457 {A T eta a b : ℝ}
    (hA : 0 < A) (hT : 0 < T) (heta : 0 < eta) (hhalf : eta ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0165.d007234 (Real.exp (-A)) eta a / (2 * T) *
      (∫ u in eta..(1 - eta), ∫ x in a..b, ∫ r in A..(A + T), _root_.GD.N0168.d022365 u x g r) ≤
        _root_.GD.N0174.d022397 A T g := by
  have hAB : A ≤ A + T := by linarith
  let μ := (volume.restrict (Ioc A (A + T))).prod (_root_.GD.N0198.d022440 eta a b)
  have hs := _root_.GD.N0198.d022448 (B := A + T) (b := b) hA heta ha g hg h01
  have he := _root_.GD.N0198.d022456 (B := A + T) (b := b) hA heta ha g hg h01
  have hp : _root_.GD.N0165.d007234 (Real.exp (-A)) eta a *
      (∫ z, _root_.GD.N0168.d022365 z.2.1 z.2.2 g z.1 ∂μ) ≤ ∫ z, _root_.GD.N0198.d022442 g z.1 z.2 ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_mono_ae (he.const_mul _) hs
    filter_upwards [_root_.GD.N0198.d022449 A (A + T) eta a b] with z hz
    exact _root_.GD.N0198.d022455 hA heta ha hz.1.1.le
      hz.2.1.1.le hz.2.1.2 hz.2.2.1.le g
  have hsi : (∫ z, _root_.GD.N0198.d022442 g z.1 z.2 ∂μ) =
      ∫ r in A..(A + T), ∫ p, _root_.GD.N0198.d022442 g r p ∂_root_.GD.N0198.d022440 eta a b := by
    simpa only [intervalIntegral.integral_of_le hAB] using
      (MeasureTheory.integral_prod (fun z => _root_.GD.N0198.d022442 g z.1 z.2) hs)
  have hei : (∫ z, _root_.GD.N0168.d022365 z.2.1 z.2.2 g z.1 ∂μ) =
      ∫ u in eta..(1 - eta), ∫ x in a..b, ∫ r in A..(A + T), _root_.GD.N0168.d022365 u x g r := by
    calc
      _ = ∫ r in A..(A + T), ∫ p, _root_.GD.N0168.d022365 p.1 p.2 g r ∂_root_.GD.N0198.d022440 eta a b := by
        simpa only [intervalIntegral.integral_of_le hAB] using
          (MeasureTheory.integral_prod
            (fun z : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0168.d022365 z.2.1 z.2.2 g z.1) he)
      _ = _ := _root_.GD.N0198.d022450 hAB hhalf hab he
  calc
    _ = (1 / (2 * T)) * (_root_.GD.N0165.d007234 (Real.exp (-A)) eta a *
        (∫ z, _root_.GD.N0168.d022365 z.2.1 z.2.2 g z.1 ∂μ)) := by rw [hei]; ring
    _ ≤ (1 / (2 * T)) * ∫ z, _root_.GD.N0198.d022442 g z.1 z.2 ∂μ :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _root_.GD.N0198.d022443 eta a b A T g := by rw [hsi]; rfl
    _ ≤ _ := _root_.GD.N0198.d022453 hA hT heta hhalf ha hab g hg h01

end
end GD.N0198

#print axioms _root_.GD.N0198.d022444
#print axioms _root_.GD.N0198.d022445
#print axioms _root_.GD.N0198.d022448
#print axioms _root_.GD.N0198.d022451
#print axioms _root_.GD.N0198.d022452
#print axioms _root_.GD.N0198.d022453
#print axioms _root_.GD.N0198.d022454
#print axioms _root_.GD.N0198.d022455
#print axioms _root_.GD.N0198.d022456
#print axioms _root_.GD.N0198.d022457
