import GD.Module0278













open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1290

noncomputable section

abbrev d004131 := Icc (0 : ℝ) 1


def d004132 (q : ℝ) (phi P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (v : ℝ) : ℝ :=
  ∫ t, phi t * (P t + v * H t) ^ (-q) ∂mu

private theorem d004133 {P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} {L v : ℝ}
    (hL : 0 < L) (hP : ∀ t, L ≤ P t) (hH : ∀ t, |H t| ≤ 1)
    (hv : |v| < L / 2) (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < P t + v * H t := by
  have hprod : |v * H t| < L / 2 := by
    rw [abs_mul]
    calc
      |v| * |H t| ≤ |v| * 1 :=
        mul_le_mul_of_nonneg_left (hH t) (abs_nonneg v)
      _ = |v| := mul_one _
      _ < L / 2 := hv
  linarith [hP t, (abs_lt.mp hprod).1]

private theorem d004134 (q : ℝ)
    {phi P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi) (hP : Continuous P)
    (hpos : ∀ t, 0 < P t) :
    Continuous (fun t ↦ phi t * (P t) ^ (-q)) := by
  apply hphi.mul
  exact hP.rpow_const fun t ↦ Or.inl (ne_of_gt (hpos t))

theorem d004135 (q : ℝ)
    {phi P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi) (hP : Continuous P)
    (hpos : ∀ t, 0 < P t) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] :
    Integrable (fun t ↦ phi t * (P t) ^ (-q)) mu :=
  (_root_.GD.N0232.N0720.N1290.d004134 q hphi hP hpos).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact



theorem d004136 (q : ℝ) (phi P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hphi : Continuous phi) (hP : Continuous P) (hH : Continuous H)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {L : ℝ} (hL : 0 < L) (hPlower : ∀ t, L ≤ P t)
    (hHbound : ∀ t, |H t| ≤ 1) :
    HasDerivAt (_root_.GD.N0232.N0720.N1290.d004132 q phi P H mu)
      (-q * ∫ t, phi t * H t * (P t) ^ (-(q + 1)) ∂mu) 0 := by
  let F : ℝ → _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun v t ↦ phi t * (P t + v * H t) ^ (-q)
  let F' : ℝ → _root_.GD.N0232.N0720.N1290.d004131 → ℝ :=
    fun v t ↦ (-q) * phi t * H t * (P t + v * H t) ^ (-q - 1)
  have hbase {v : ℝ} (hv : |v| < L / 2) (t : _root_.GD.N0232.N0720.N1290.d004131) :
      0 < P t + v * H t := _root_.GD.N0232.N0720.N1290.d004133 hL hPlower hHbound hv t
  have hpoint {v : ℝ} (hv : |v| < L / 2) (t : _root_.GD.N0232.N0720.N1290.d004131) :
      HasDerivAt (fun w ↦ F w t) (F' v t) v := by
    have hinner : HasDerivAt (fun w : ℝ ↦ P t + w * H t) (H t) v := by
      simpa only [zero_add, one_mul] using
        (hasDerivAt_const v (P t)).fun_add ((hasDerivAt_id' v).mul_const (H t))
    have hpow := hinner.rpow_const (p := -q) (Or.inl (ne_of_gt (hbase hv t)))
    have hraw := (hasDerivAt_const v (phi t)).mul hpow
    convert hraw using 1
    · ext <;> rfl
    · ext <;> rfl
    · funext w
      rfl
    · dsimp [F']
      ring
  have hcontF {v : ℝ} (hv : |v| < L / 2) : Continuous (F v) := by
    dsimp [F]
    apply hphi.mul
    exact (hP.add (continuous_const.mul hH)).rpow_const
      fun t ↦ Or.inl (ne_of_gt (hbase hv t))
  have hcontF' : ContinuousOn (fun vt : ℝ × _root_.GD.N0232.N0720.N1290.d004131 ↦ F' vt.1 vt.2)
      (Icc (-(L / 4)) (L / 4) ×ˢ (Set.univ : Set _root_.GD.N0232.N0720.N1290.d004131)) := by
    dsimp [F']
    apply ContinuousOn.mul
    · exact ((continuous_const.mul (hphi.comp continuous_snd)).mul
        (hH.comp continuous_snd)).continuousOn
    apply ContinuousOn.rpow_const
    · exact ((hP.comp continuous_snd).add
        (continuous_fst.mul (hH.comp continuous_snd))).continuousOn
    · intro vt hvt
      apply Or.inl
      apply ne_of_gt
      apply hbase
      have hv : |vt.1| ≤ L / 4 := (abs_le).2 hvt.1
      linarith
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hcontF'
  have hzero : (0 : ℝ) ∈ Ioo (-(L / 4)) (L / 4) := by
    constructor <;> linarith
  have hzeroOuter : |(0 : ℝ)| < L / 2 := by simp; linarith
  have hcontF'zero : Continuous (F' 0) := by
    dsimp [F']
    simp only [zero_mul, add_zero]
    apply Continuous.mul
    · exact (continuous_const.mul hphi).mul hH
    exact hP.rpow_const fun t ↦ Or.inl (ne_of_gt (hL.trans_le (hPlower t)))
  have hderiv : HasDerivAt (fun v ↦ ∫ t, F v t ∂mu) (∫ t, F' 0 t ∂mu) 0 := by
    refine
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := F) (F' := F') (s := Ioo (-(L / 4)) (L / 4))
        (bound := fun _ : _root_.GD.N0232.N0720.N1290.d004131 ↦ C)
        (Ioo_mem_nhds hzero.1 hzero.2) ?_
        ((hcontF hzeroOuter).integrable_of_hasCompactSupport
          (isClosed_tsupport _).isCompact)
        hcontF'zero.aestronglyMeasurable ?_ (integrable_const C) ?_).2
    · filter_upwards [isOpen_Ioo.eventually_mem hzero] with v hv
      have hcont := hcontF (v := v) (by rw [abs_lt]; constructor <;> linarith [hv.1, hv.2])
      exact hcont.aestronglyMeasurable
    · exact ae_of_all mu fun t v hv ↦
        hC (v, t) ⟨⟨hv.1.le, hv.2.le⟩, Set.mem_univ t⟩
    · exact ae_of_all mu fun t v hv ↦
        hpoint (v := v) (by rw [abs_lt]; constructor <;> linarith [hv.1, hv.2]) t
  change HasDerivAt (fun v ↦ ∫ t, F v t ∂mu) _ 0
  convert hderiv using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp [F']
  simp only [zero_mul, add_zero]
  rw [show -(q + 1) = -q - 1 by ring]
  ring


def d004137 (q : ℝ) (P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (v : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1290.d004132 q (fun t ↦ (t : ℝ)) P H mu v /
    _root_.GD.N0232.N0720.N1290.d004132 q (fun _ ↦ 1) P H mu v



theorem d004138 (q : ℝ) (P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : Continuous P) (hH : Continuous H)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {L : ℝ} (hL : 0 < L) (hPlower : ∀ t, L ≤ P t)
    (hHbound : ∀ t, |H t| ≤ 1)
    (hD : _root_.GD.N0232.N0720.N1290.d004132 q (fun _ ↦ 1) P H mu 0 ≠ 0) :
    HasDerivAt (_root_.GD.N0232.N0720.N1290.d004137 q P H mu)
      (-q / _root_.GD.N0232.N0720.N1290.d004132 q (fun _ ↦ 1) P H mu 0 *
        ∫ t, ((t : ℝ) - _root_.GD.N0232.N0720.N1290.d004137 q P H mu 0) * H t *
          (P t) ^ (-(q + 1)) ∂mu) 0 := by
  have hN := _root_.GD.N0232.N0720.N1290.d004136 q (fun t ↦ (t : ℝ)) P H
    continuous_subtype_val hP hH mu hL hPlower hHbound
  have hMass := _root_.GD.N0232.N0720.N1290.d004136 q (fun _ ↦ 1) P H
    continuous_const hP hH mu hL hPlower hHbound
  have hpos (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < P t := hL.trans_le (hPlower t)
  have hiN : Integrable (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ) * H t *
      (P t) ^ (-(q + 1))) mu :=
    _root_.GD.N0232.N0720.N1290.d004135 (q + 1)
      (continuous_subtype_val.mul hH) hP hpos mu
  have hiH : Integrable (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ H t * (P t) ^ (-(q + 1))) mu :=
    _root_.GD.N0232.N0720.N1290.d004135 (q + 1) hH hP hpos mu
  have hcenter :
      (∫ t, ((t : ℝ) - _root_.GD.N0232.N0720.N1290.d004137 q P H mu 0) * H t *
        (P t) ^ (-(q + 1)) ∂mu) =
      (∫ t, (t : ℝ) * H t * (P t) ^ (-(q + 1)) ∂mu) -
        _root_.GD.N0232.N0720.N1290.d004137 q P H mu 0 *
          ∫ t, H t * (P t) ^ (-(q + 1)) ∂mu := by
    calc
      _ = ∫ t, (t : ℝ) * H t * (P t) ^ (-(q + 1)) -
          _root_.GD.N0232.N0720.N1290.d004137 q P H mu 0 * (H t * (P t) ^ (-(q + 1))) ∂mu := by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = _ := by rw [integral_sub hiN (hiH.const_mul _), integral_const_mul]
  have hraw := hN.div hMass hD
  change HasDerivAt (_root_.GD.N0232.N0720.N1290.d004137 q P H mu) _ 0 at hraw
  convert hraw using 1
  rw [hcenter]
  simp only [one_mul]
  unfold _root_.GD.N0232.N0720.N1290.d004137
  field_simp [hD]
  ring


def d004139 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  ∫ t, (P t) ^ (-q) ∂mu


def d004140 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  (∫ t, (t : ℝ) * (P t) ^ (-q) ∂mu) / _root_.GD.N0232.N0720.N1290.d004139 q P mu

@[simp] theorem d004141 (q : ℝ) (P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) :
    _root_.GD.N0232.N0720.N1290.d004132 q (fun _ ↦ 1) P H mu 0 = _root_.GD.N0232.N0720.N1290.d004139 q P mu := by
  simp [_root_.GD.N0232.N0720.N1290.d004132, _root_.GD.N0232.N0720.N1290.d004139]

@[simp] theorem d004142 (q : ℝ) (P H : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1290.d004137 q P H mu 0 = _root_.GD.N0232.N0720.N1290.d004140 q P mu := by
  simp [_root_.GD.N0232.N0720.N1290.d004137, _root_.GD.N0232.N0720.N1290.d004132, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139]



def d004143 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  (_root_.GD.N0232.N0720.N1290.d004140 q P mu) ^ 2 *
      deriv (_root_.GD.N0232.N0720.N1290.d004137 q P (fun t ↦ 1 - (t : ℝ)) mu) 0 +
    (1 - _root_.GD.N0232.N0720.N1290.d004140 q P mu) ^ 2 *
      deriv (_root_.GD.N0232.N0720.N1290.d004137 q P (fun t ↦ (t : ℝ)) mu) 0 -
    deriv (_root_.GD.N0232.N0720.N1290.d004137 q P (fun t ↦ (t : ℝ) * (1 - (t : ℝ))) mu) 0



theorem d004144 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : Continuous P) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {L : ℝ} (hL : 0 < L) (hPlower : ∀ t, L ≤ P t)
    (hD : _root_.GD.N0232.N0720.N1290.d004139 q P mu ≠ 0) :
    _root_.GD.N0232.N0720.N1290.d004143 q P mu = -q / _root_.GD.N0232.N0720.N1290.d004139 q P mu *
      ∫ t, ((t : ℝ) - _root_.GD.N0232.N0720.N1290.d004140 q P mu) ^ 3 *
        (P t) ^ (-(q + 1)) ∂mu := by
  have hzbound (t : _root_.GD.N0232.N0720.N1290.d004131) : |1 - (t : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr t.2.2)]
    linarith [t.2.1]
  have hwbound (t : _root_.GD.N0232.N0720.N1290.d004131) : |(t : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg t.2.1]
    exact t.2.2
  have hubound (t : _root_.GD.N0232.N0720.N1290.d004131) : |(t : ℝ) * (1 - (t : ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2))]
    nlinarith [t.2.1, t.2.2, sq_nonneg (t : ℝ)]
  have hz := (_root_.GD.N0232.N0720.N1290.d004138 q P (fun t ↦ 1 - (t : ℝ))
    hP (by fun_prop) mu hL hPlower hzbound (by simpa using hD)).deriv
  have hw := (_root_.GD.N0232.N0720.N1290.d004138 q P (fun t ↦ (t : ℝ))
    hP continuous_subtype_val mu hL hPlower hwbound (by simpa using hD)).deriv
  have hu := (_root_.GD.N0232.N0720.N1290.d004138 q P (fun t ↦ (t : ℝ) * (1 - (t : ℝ)))
    hP (by fun_prop) mu hL hPlower hubound (by simpa using hD)).deriv
  simp only [_root_.GD.N0232.N0720.N1290.d004141, _root_.GD.N0232.N0720.N1290.d004142] at hz hw hu
  let g := _root_.GD.N0232.N0720.N1290.d004140 q P mu
  let K : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ (P t) ^ (-(q + 1))
  let Z : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ ((t : ℝ) - g) * (1 - (t : ℝ)) * K t
  let W : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ ((t : ℝ) - g) * (t : ℝ) * K t
  let U : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ ((t : ℝ) - g) * ((t : ℝ) * (1 - (t : ℝ))) * K t
  have hpos (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < P t := hL.trans_le (hPlower t)
  have hiZ : Integrable Z mu :=
    _root_.GD.N0232.N0720.N1290.d004135 (q + 1) (by fun_prop) hP hpos mu
  have hiW : Integrable W mu :=
    _root_.GD.N0232.N0720.N1290.d004135 (q + 1) (by fun_prop) hP hpos mu
  have hiU : Integrable U mu :=
    _root_.GD.N0232.N0720.N1290.d004135 (q + 1) (by fun_prop) hP hpos mu
  have hcubic :
      g ^ 2 * (∫ t, Z t ∂mu) + (1 - g) ^ 2 * (∫ t, W t ∂mu) -
        (∫ t, U t ∂mu) = ∫ t, ((t : ℝ) - g) ^ 3 * K t ∂mu := by
    calc
      _ = ∫ t, g ^ 2 * Z t + (1 - g) ^ 2 * W t - U t ∂mu := by
        rw [integral_sub (f := fun t ↦ g ^ 2 * Z t + (1 - g) ^ 2 * W t) (g := U)
            ((hiZ.const_mul (g ^ 2)).add (hiW.const_mul ((1 - g) ^ 2))) hiU,
          integral_add (f := fun t ↦ g ^ 2 * Z t) (g := fun t ↦ (1 - g) ^ 2 * W t)
            (hiZ.const_mul _) (hiW.const_mul _),
          integral_const_mul, integral_const_mul]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [Z, W, U]
        ring
  unfold _root_.GD.N0232.N0720.N1290.d004143
  rw [hz, hw, hu]
  change g ^ 2 * (-q / _root_.GD.N0232.N0720.N1290.d004139 q P mu * ∫ t, Z t ∂mu) +
      (1 - g) ^ 2 * (-q / _root_.GD.N0232.N0720.N1290.d004139 q P mu * ∫ t, W t ∂mu) -
      (-q / _root_.GD.N0232.N0720.N1290.d004139 q P mu * ∫ t, U t ∂mu) = _
  calc
    _ = -q / _root_.GD.N0232.N0720.N1290.d004139 q P mu *
        (g ^ 2 * (∫ t, Z t ∂mu) + (1 - g) ^ 2 * (∫ t, W t ∂mu) -
          (∫ t, U t ∂mu)) := by ring
    _ = _ := by rw [hcubic]



theorem d004145 (q : ℝ) (hq : q ≠ 0)
    (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (hP : Continuous P)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {L : ℝ} (hL : 0 < L) (hPlower : ∀ t, L ≤ P t)
    (hD : _root_.GD.N0232.N0720.N1290.d004139 q P mu ≠ 0) (hF : _root_.GD.N0232.N0720.N1290.d004143 q P mu = 0) :
    (∫ t, ((t : ℝ) - _root_.GD.N0232.N0720.N1290.d004140 q P mu) ^ 3 * (P t) ^ (-(q + 1)) ∂mu) = 0 := by
  rw [_root_.GD.N0232.N0720.N1290.d004144 q P hP mu hL hPlower hD] at hF
  exact (mul_eq_zero.mp hF).resolve_left (div_ne_zero (neg_ne_zero.mpr hq) hD)


theorem d004146 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (hP : Continuous P)
    (hpos : ∀ t, 0 < P t) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    0 < _root_.GD.N0232.N0720.N1290.d004139 q P mu := by
  have hi : Integrable (fun t ↦ (P t) ^ (-q)) mu := by
    simpa using _root_.GD.N0232.N0720.N1290.d004135 q continuous_const hP hpos mu
      (phi := fun _ ↦ 1)
  have hnonneg : 0 ≤ (fun t ↦ (P t) ^ (-q)) :=
    fun t ↦ (Real.rpow_pos_of_pos (hpos t) _).le
  have hsupp : Function.support (fun t ↦ (P t) ^ (-q)) = Set.univ := by
    ext t
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (Real.rpow_pos_of_pos (hpos t) _)
  unfold _root_.GD.N0232.N0720.N1290.d004139
  rw [integral_pos_iff_support_of_nonneg hnonneg hi, hsupp]
  simp

open _root_.GD.N0232.N0720.N1413 _root_.GD.N0232.N0720.N1415


def d004147 (center epsilon : ℝ) (t : _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  1 - epsilon * ((t : ℝ) - center)

private theorem d004148 (center : ℝ) {epsilon : ℝ}
    (he : |epsilon| < _root_.GD.N0232.N0720.N1413.d004097 0 1 center) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    (1 / 2 : ℝ) ≤ _root_.GD.N0232.N0720.N1290.d004147 center epsilon t := by
  have hB := _root_.GD.N0232.N0720.N1413.d004096 0 1 center
  have ht : |(t : ℝ) - center| ≤ _root_.GD.N0232.N0720.N1413.d004095 0 1 center := by
    calc
      |(t : ℝ) - center| ≤ |(t : ℝ)| + |center| := abs_sub _ _
      _ ≤ _root_.GD.N0232.N0720.N1413.d004095 0 1 center := by
        rw [abs_of_nonneg t.2.1]
        simp only [_root_.GD.N0232.N0720.N1413.d004095, abs_zero, abs_one]
        linarith [t.2.2]
  have hrad : _root_.GD.N0232.N0720.N1413.d004097 0 1 center * _root_.GD.N0232.N0720.N1413.d004095 0 1 center = (1 / 2 : ℝ) := by
    unfold _root_.GD.N0232.N0720.N1413.d004097
    field_simp [ne_of_gt hB]
  have hprod : |epsilon * ((t : ℝ) - center)| < (1 / 2 : ℝ) := by
    rw [abs_mul]
    calc
      |epsilon| * |(t : ℝ) - center| ≤
          |epsilon| * _root_.GD.N0232.N0720.N1413.d004095 0 1 center :=
        mul_le_mul_of_nonneg_left ht (abs_nonneg epsilon)
      _ < _root_.GD.N0232.N0720.N1413.d004097 0 1 center * _root_.GD.N0232.N0720.N1413.d004095 0 1 center :=
        mul_lt_mul_of_pos_right he hB
      _ = (1 / 2 : ℝ) := hrad
  unfold _root_.GD.N0232.N0720.N1290.d004147
  linarith [(abs_lt.mp hprod).2]



theorem d004149
    (center epsilon q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    (hpos : ∀ t, 0 < _root_.GD.N0232.N0720.N1290.d004147 center epsilon t)
    (hD : _root_.GD.N0232.N0720.N1290.d004139 q (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) mu ≠ 0) :
    _root_.GD.N0232.N0720.N1413.d004128 0 1 center q mu epsilon =
      (_root_.GD.N0232.N0720.N1290.d004139 q (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) mu) ^ 3 *
        ∫ t, ((t : ℝ) - _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) mu) ^ 3 *
          (_root_.GD.N0232.N0720.N1290.d004147 center epsilon t) ^ (-(q + 1)) ∂mu := by
  let P := _root_.GD.N0232.N0720.N1290.d004147 center epsilon
  let M := _root_.GD.N0232.N0720.N1290.d004139 q P mu
  let B := _root_.GD.N0232.N0720.N1413.d004111 0 1 center q 1 mu epsilon
  let K : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ (P t) ^ (-(q + 1))
  let A : ℕ → _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun j t ↦ ((t : ℝ) - center) ^ j * K t
  have hP : Continuous P := by
    change Continuous (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ 1 - epsilon * ((t : ℝ) - center))
    fun_prop
  have hM : _root_.GD.N0232.N0720.N1413.d004111 0 1 center q 0 mu epsilon = M := by
    simp [_root_.GD.N0232.N0720.N1413.d004111, M, _root_.GD.N0232.N0720.N1290.d004139, P, _root_.GD.N0232.N0720.N1290.d004147]
  have hi (j : ℕ) : Integrable (A j) mu :=
    _root_.GD.N0232.N0720.N1290.d004135 (q + 1) (by fun_prop) hP hpos mu
  have hiMass : Integrable (fun t ↦ (P t) ^ (-q)) mu := by
    simpa using _root_.GD.N0232.N0720.N1290.d004135 q continuous_const hP hpos mu
      (phi := fun _ ↦ 1)
  have hiFirst : Integrable (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ ((t : ℝ) - center) * (P t) ^ (-q)) mu :=
    _root_.GD.N0232.N0720.N1290.d004135 q (by fun_prop) hP hpos mu
  have hNum : (∫ t : _root_.GD.N0232.N0720.N1290.d004131, (t : ℝ) * (P t) ^ (-q) ∂mu) = center * M + B := by
    calc
      _ = ∫ t : _root_.GD.N0232.N0720.N1290.d004131, center * (P t) ^ (-q) +
          ((t : ℝ) - center) * (P t) ^ (-q) ∂mu := by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = _ := by
        rw [integral_add (hiMass.const_mul center) hiFirst, integral_const_mul]
        simp [M, B, _root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1413.d004111, P, _root_.GD.N0232.N0720.N1290.d004147]
  have hMean : _root_.GD.N0232.N0720.N1290.d004140 q P mu = center + B / M := by
    unfold _root_.GD.N0232.N0720.N1290.d004140
    rw [hNum]
    change (center * M + B) / M = center + B / M
    field_simp [show M ≠ 0 from hD]
  have hAj (j : ℕ) : _root_.GD.N0232.N0720.N1413.d004111 0 1 center (q + 1) j mu epsilon =
      ∫ t, A j t ∂mu := rfl
  have hC : _root_.GD.N0232.N0720.N1413.d004128 0 1 center q mu epsilon =
      M ^ 3 * (∫ t, A 3 t ∂mu) - (3 * B * M ^ 2) * (∫ t, A 2 t ∂mu) +
        (3 * B ^ 2 * M) * (∫ t, A 1 t ∂mu) - B ^ 3 * (∫ t, A 0 t ∂mu) := by
    simp only [_root_.GD.N0232.N0720.N1413.d004128, _root_.GD.N0232.N0720.N1413.d004126, Pi.sub_apply, Pi.add_apply,
      Pi.mul_apply, Pi.pow_apply, hM, hAj]
    change M ^ 3 * (∫ t, A 3 t ∂mu) - 3 * (B * M ^ 2 * (∫ t, A 2 t ∂mu)) +
      3 * (B ^ 2 * M * (∫ t, A 1 t ∂mu)) - B ^ 3 * (∫ t, A 0 t ∂mu) = _
    ring
  rw [hC]
  calc
    _ = ∫ t, M ^ 3 * A 3 t - (3 * B * M ^ 2) * A 2 t +
        (3 * B ^ 2 * M) * A 1 t - B ^ 3 * A 0 t ∂mu := by
      rw [integral_sub
          (f := fun t ↦ M ^ 3 * A 3 t - (3 * B * M ^ 2) * A 2 t +
            (3 * B ^ 2 * M) * A 1 t) (g := fun t ↦ B ^ 3 * A 0 t)
          ((((hi 3).const_mul _).sub ((hi 2).const_mul _)).add ((hi 1).const_mul _))
          ((hi 0).const_mul _),
        integral_add (f := fun t ↦ M ^ 3 * A 3 t - (3 * B * M ^ 2) * A 2 t)
          (g := fun t ↦ (3 * B ^ 2 * M) * A 1 t)
          (((hi 3).const_mul _).sub ((hi 2).const_mul _))
          ((hi 1).const_mul _),
        integral_sub (f := fun t ↦ M ^ 3 * A 3 t) (g := fun t ↦ (3 * B * M ^ 2) * A 2 t)
          ((hi 3).const_mul _) ((hi 2).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      change M ^ 3 * A 3 t - (3 * B * M ^ 2) * A 2 t +
        (3 * B ^ 2 * M) * A 1 t - B ^ 3 * A 0 t =
        M ^ 3 * (((t : ℝ) - _root_.GD.N0232.N0720.N1290.d004140 q P mu) ^ 3 * K t)
      rw [hMean]
      dsimp [A]
      field_simp [show M ≠ 0 from hD]
      ring




theorem d004150
    (center q : ℝ) (hq : q ≠ 0)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hF : ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) mu = 0) :
    _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 0 1 center mu) = 0 := by
  apply _root_.GD.N0232.N0720.N1413.d004130 0 1 center q mu
  have hzero : (0 : ℝ) ∈ Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 0 1 center)) (_root_.GD.N0232.N0720.N1413.d004097 0 1 center) := by
    have hr := _root_.GD.N0232.N0720.N1413.d004098 0 1 center
    constructor <;> linarith
  filter_upwards [hF, isOpen_Ioo.eventually_mem hzero] with epsilon heF he
  have hPlower : ∀ t, (1 / 2 : ℝ) ≤ _root_.GD.N0232.N0720.N1290.d004147 center epsilon t :=
    _root_.GD.N0232.N0720.N1290.d004148 center ((abs_lt).2 he)
  have hpos (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < _root_.GD.N0232.N0720.N1290.d004147 center epsilon t := by
    linarith [hPlower t]
  have hP : Continuous (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) := by
    unfold _root_.GD.N0232.N0720.N1290.d004147
    fun_prop
  have hD : _root_.GD.N0232.N0720.N1290.d004139 q (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) mu ≠ 0 :=
    ne_of_gt (_root_.GD.N0232.N0720.N1290.d004146 q _ hP hpos mu)
  rw [_root_.GD.N0232.N0720.N1290.d004149 center epsilon q mu hpos hD,
    _root_.GD.N0232.N0720.N1290.d004145 q hq _ hP mu
      (by norm_num : (0 : ℝ) < 1 / 2) hPlower hD heF, mul_zero]

end

end GD.N0232.N0720.N1290

#print axioms _root_.GD.N0232.N0720.N1290.d004136
#print axioms _root_.GD.N0232.N0720.N1290.d004138
#print axioms _root_.GD.N0232.N0720.N1290.d004144
#print axioms _root_.GD.N0232.N0720.N1290.d004150
