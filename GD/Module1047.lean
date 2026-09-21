import Mathlib.MeasureTheory.Function.ContinuousMapDense
import GD.Module1046
import GD.Module1034
























open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Topology

namespace GD
namespace N0232
namespace N0720
namespace N1198

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1199
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0708
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0945
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229





theorem d016704
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (v : H) (R : ℝ)
    (hu : ∀ j, ‖u j‖ ≤ R) (hv : ‖v‖ ≤ R)
    (D : Set H) (hD : Dense D)
    (hprobe : ∀ φ ∈ D, Tendsto (fun j ↦ ⟪φ, u j⟫) atTop (𝓝 ⟪φ, v⟫))
    (w : H) :
    Tendsto (fun j ↦ ⟪w, u j⟫) atTop (𝓝 ⟪w, v⟫) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (hv)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (3 * (R + 1)) := by positivity
  obtain ⟨φ, hφ, hφD⟩ := Metric.dense_iff.1 hD w _ hδ
  rw [Metric.mem_ball, dist_eq_norm] at hφ
  have h := hprobe φ hφD
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (ε / 3) (by positivity)
  refine ⟨N, fun j hj ↦ ?_⟩
  have h1 : |⟪w - φ, u j⟫| ≤ ε / 3 := by
    calc |⟪w - φ, u j⟫| ≤ ‖w - φ‖ * ‖u j‖ := abs_real_inner_le_norm _ _
      _ ≤ (ε / (3 * (R + 1))) * R := by
          rw [norm_sub_rev]
          apply mul_le_mul hφ.le (hu j) (norm_nonneg _) hδ.le
      _ ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have h2 : |⟪φ - w, v⟫| ≤ ε / 3 := by
    calc |⟪φ - w, v⟫| ≤ ‖φ - w‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (ε / (3 * (R + 1))) * R := by
          apply mul_le_mul hφ.le hv (norm_nonneg _) hδ.le
      _ ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have h3 := hN j hj
  rw [Real.dist_eq] at h3 ⊢
  have hsplit : ⟪w, u j⟫ - ⟪w, v⟫ =
      ⟪w - φ, u j⟫ + (⟪φ, u j⟫ - ⟪φ, v⟫) + ⟪φ - w, v⟫ := by
    simp only [inner_sub_left]
    ring
  rw [hsplit]
  calc |⟪w - φ, u j⟫ + (⟪φ, u j⟫ - ⟪φ, v⟫) + ⟪φ - w, v⟫|
      ≤ |⟪w - φ, u j⟫| + |⟪φ, u j⟫ - ⟪φ, v⟫| + |⟪φ - w, v⟫| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring





theorem d016705
    {X : Type*} [TopologicalSpace X]
    (loc : X → ℝ) (scale : X → ℝ) (y : X → ℝ)
    (hloc : Continuous loc) (hscale : Continuous scale)
    (hpos : ∀ p, 0 < scale p) (hy : Continuous y) :
    Continuous (fun p : X ↦ _root_.GD.N0232.N0719.N0932.d009204 (loc p) (scale p) (y p)) := by
  have hfun : (fun p : X ↦ _root_.GD.N0232.N0719.N0932.d009204 (loc p) (scale p) (y p)) =
      fun p : X ↦ (scale p)⁻¹ * Real.exp
        (y p ^ 2 / 2 - (y p - loc p) ^ 2 / (2 * scale p ^ 2)) := by
    funext p
    exact _root_.GD.N0232.N0720.N1124.d016497 (loc p) (scale p) (y p) (hpos p)
  rw [hfun]
  have hne : ∀ p, scale p ≠ 0 := fun p ↦ (hpos p).ne'
  refine (hscale.inv₀ hne).mul (Real.continuous_exp.comp ?_)
  refine ((hy.pow 2).div_const 2).sub ?_
  exact ((hy.sub hloc).pow 2).div (continuous_const.mul (hscale.pow 2))
    (fun p ↦ by have := hne p; positivity)



theorem d016706
    {X : Type*} [TopologicalSpace X] (k : ℕ)
    (loc : X → ℝ) (scale : X → ℝ) (x : X → Fin k → ℝ)
    (hloc : Continuous loc) (hscale : Continuous scale)
    (hpos : ∀ p, 0 < scale p) (hx : Continuous x) :
    Continuous (fun p : X ↦ _root_.GD.N0232.N0719.N0932.d009213 k (loc p) (scale p) (x p)) := by
  have hfun : (fun p : X ↦ _root_.GD.N0232.N0719.N0932.d009213 k (loc p) (scale p) (x p)) =
      fun p : X ↦ ∏ i : Fin k, _root_.GD.N0232.N0719.N0932.d009204 (loc p) (scale p) (x p i) := by
    funext p
    unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
    rfl
  rw [hfun]
  apply continuous_finsetProd
  intro i _
  exact _root_.GD.N0232.N0720.N1198.d016705 loc scale (fun p ↦ x p i)
    hloc hscale hpos ((continuous_apply i).comp hx)

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



theorem d016707 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n p.1 p.2) := by
  have hloc : Continuous (fun p : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1.location) :=
    _root_.GD.N0232.N0720.N1499.d014998.comp continuous_fst
  have hs₁ : Continuous (fun p : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1.scale₁) :=
    _root_.GD.N0232.N0720.N1499.d014999.comp continuous_fst
  have hs₂ : Continuous (fun p : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1.scale₂) :=
    _root_.GD.N0232.N0720.N1499.d015000.comp continuous_fst
  have h₁ := _root_.GD.N0232.N0720.N1198.d016706 m
    (fun p : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1.location)
    (fun p ↦ p.1.scale₁) (fun p ↦ p.2.1) hloc hs₁ (fun p ↦ p.1.scale₁_pos)
    (continuous_fst.comp continuous_snd)
  have h₂ := _root_.GD.N0232.N0720.N1198.d016706 n
    (fun p : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1.location)
    (fun p ↦ p.1.scale₂) (fun p ↦ p.2.2) hloc hs₂ (fun p ↦ p.1.scale₂_pos)
    (continuous_snd.comp continuous_snd)
  exact h₁.mul h₂


theorem d016708 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1 • p.2) := by
  have hshift : Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1.shift) :=
    _root_.GD.N0232.N0719.N0945.d009267.comp continuous_fst
  have hdil : Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1.d009239) :=
    _root_.GD.N0232.N0719.N0945.d009268.comp continuous_fst
  change Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦
    _root_.GD.N0107.d009024 m n p.1.shift p.1.d009239 p.1.d009239 p.2)
  unfold _root_.GD.N0107.d009024 _root_.GD.N0107.d009018
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact hshift.add (hdil.mul ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))
  · apply continuous_pi
    intro i
    exact hshift.add (hdil.mul ((continuous_apply i).comp (continuous_snd.comp continuous_snd)))


theorem d016709 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Continuous (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • y) := by
  have hpair : Continuous (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
      ((g, y) : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n)) :=
    continuous_const.prodMk continuous_id
  have := (_root_.GD.N0232.N0720.N1198.d016708 m n).comp hpair
  exact this


theorem d016710 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Continuous (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ _root_.GD.N0232.N0720.N1499.d015001 m n theta y) := by
  have hpair : Continuous (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
      ((theta, y) : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n)) :=
    continuous_const.prodMk continuous_id
  have := (_root_.GD.N0232.N0720.N1198.d016707 m n).comp hpair
  exact this

theorem d016711 (g : _root_.GD.N0232.N0720.N1025.d014301) (x : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    g⁻¹ • (g • x) = x := by
  rw [smul_smul, inv_mul_cancel, one_smul]

theorem d016712 (g : _root_.GD.N0232.N0720.N1025.d014301) (x : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    g • (g⁻¹ • x) = x := by
  rw [smul_smul, mul_inv_cancel, one_smul]






def d016713 (g : _root_.GD.N0232.N0720.N1025.d014301) (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun y ↦ φ (g • y) *
    _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) y

theorem d016714 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Continuous φ) :
    Continuous (_root_.GD.N0232.N0720.N1198.d016713 m n g φ) := by
  have hact : Continuous (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • y) :=
    _root_.GD.N0232.N0720.N1198.d016709 m n g
  have hlik : Continuous (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) y) :=
    _root_.GD.N0232.N0720.N1198.d016710 m n _
  exact (hφ.comp hact).mul hlik

theorem d016715 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (_root_.GD.N0232.N0720.N1198.d016713 m n g φ) := by
  apply HasCompactSupport.intro (hφ.image (_root_.GD.N0232.N0720.N1198.d016709 m n g⁻¹))
  intro x hx
  unfold _root_.GD.N0232.N0720.N1198.d016713
  by_contra hne
  have hφx : φ (g • x) ≠ 0 := fun h ↦ hne (by rw [h, zero_mul])
  have hmem : g • x ∈ tsupport φ := subset_tsupport φ hφx
  apply hx
  exact ⟨g • x, hmem, _root_.GD.N0232.N0720.N1198.d016711 m n g x⟩

theorem d016716 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    MemLp (_root_.GD.N0232.N0720.N1198.d016713 m n g φ) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  obtain ⟨C, hC⟩ := (_root_.GD.N0232.N0720.N1198.d016714 m n g φ hφ).bounded_above_of_compact_support
    (_root_.GD.N0232.N0720.N1198.d016715 m n g φ hφs)
  exact MemLp.of_bound (_root_.GD.N0232.N0720.N1198.d016714 m n g φ hφ).aestronglyMeasurable C
    (Eventually.of_forall hC)



theorem d016717
    (g : _root_.GD.N0232.N0720.N1025.d014301) (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hf : Measurable f)
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Measurable φ) :
    ∫ ω, f (g⁻¹ • ω) * φ ω ∂(_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∫ y, f y * _root_.GD.N0232.N0720.N1198.d016713 m n g φ y ∂(_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hlaw : (_root_.GD.N0232.N0720.N1080.d014172 m n).map (fun ω ↦ g⁻¹ • ω) =
      _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) := by
    have := _root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1214.d014259] using this
  have hmeas_act : Measurable (fun ω : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • ω) := by
    change Measurable (fun ω : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
      _root_.GD.N0107.d009024 m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239 ω)
    fun_prop
  have hint_meas : Measurable (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ f y * φ (g • y)) := by
    have : Measurable (fun y : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • y) := by
      change Measurable (fun ω : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
        _root_.GD.N0107.d009024 m n g.shift g.d009239 g.d009239 ω)
      fun_prop
    exact hf.mul (hφ.comp this)
  calc ∫ ω, f (g⁻¹ • ω) * φ ω ∂(_root_.GD.N0232.N0720.N1080.d014172 m n)
      = ∫ ω, (fun y ↦ f y * φ (g • y)) (g⁻¹ • ω) ∂(_root_.GD.N0232.N0720.N1080.d014172 m n) := by
        congr 1
        funext ω
        simp only [_root_.GD.N0232.N0720.N1198.d016712]
    _ = ∫ y, f y * φ (g • y) ∂((_root_.GD.N0232.N0720.N1080.d014172 m n).map (fun ω ↦ g⁻¹ • ω)) := by
        rw [integral_map hmeas_act.aemeasurable hint_meas.aestronglyMeasurable]
    _ = ∫ y, f y * φ (g • y) ∂(_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)) := by
        rw [hlaw]
    _ = ∫ y, f y * _root_.GD.N0232.N0720.N1198.d016713 m n g φ y ∂(_root_.GD.N0232.N0720.N1080.d014172 m n) := by
        rw [_root_.GD.N0232.N0720.N1499.d015006,
          integral_withDensity_eq_integral_toReal_smul
            (_root_.GD.N0232.N0720.N1499.d015002 m n _).ennreal_ofReal
            (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
        congr 1
        funext y
        rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1499.d015003 m n _ y)]
        unfold _root_.GD.N0232.N0720.N1198.d016713
        simp only [smul_eq_mul]
        ring



theorem d016718 (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    MemLp φ 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφs
  exact MemLp.of_bound hφ.aestronglyMeasurable C (Eventually.of_forall hC)


theorem d016719 {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (u v : Lp ℝ 2 ν) : ⟪u, v⟫ = ∫ x, u x * v x ∂ν := by
  simp [L2.inner_def, RCLike.inner_apply, mul_comm]


theorem d016720 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    MemLp (fun ω ↦ _root_.GD.N0232.N0720.N1214.d014265 m n d (g⁻¹ • ω)) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have htr := _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g d hd
  have hfun : (fun ω ↦ _root_.GD.N0232.N0720.N1214.d014265 m n d (g⁻¹ • ω)) =
      fun ω ↦ g.d009239⁻¹ * (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n d) ω - g.shift) := by
    funext ω
    unfold _root_.GD.N0232.N0720.N1214.d014261
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009244]
    field_simp
    ring
  rw [hfun]
  exact (htr.sub (memLp_const g.shift)).const_mul _




theorem d016721
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    ⟪(_root_.GD.N0232.N0720.N1198.d016718 m n φ hφ hφs).toLp φ,
        _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hd⟫ =
      g.shift * ∫ ω, φ ω ∂(_root_.GD.N0232.N0720.N1080.d014172 m n) +
        g.d009239 * ⟪d, (_root_.GD.N0232.N0720.N1198.d016716 m n g φ hφ hφs).toLp (_root_.GD.N0232.N0720.N1198.d016713 m n g φ)⟫ := by
  have hφ2 := _root_.GD.N0232.N0720.N1198.d016718 m n φ hφ hφs
  have hpull := _root_.GD.N0232.N0720.N1198.d016720 m n hm hn g d hd
  have hφint : Integrable φ (_root_.GD.N0232.N0720.N1080.d014172 m n) := hφ2.integrable one_le_two
  have hprod : Integrable (fun ω ↦ _root_.GD.N0232.N0720.N1214.d014265 m n d (g⁻¹ • ω) * φ ω)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := hpull.integrable_mul hφ2
  rw [_root_.GD.N0232.N0720.N1198.d016719, _root_.GD.N0232.N0720.N1198.d016719]
  have h1 : ∫ ω, ((_root_.GD.N0232.N0720.N1198.d016718 m n φ hφ hφs).toLp φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) ω *
      (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hd : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) ω ∂(_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∫ ω, g.shift * φ ω + g.d009239 * (_root_.GD.N0232.N0720.N1214.d014265 m n d (g⁻¹ • ω) * φ ω)
        ∂(_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply integral_congr_ae
    filter_upwards [hφ2.coeFn_toLp,
      (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g d hd).coeFn_toLp] with ω h₁ h₂
    have h₂' : (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hd : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) ω =
        _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n d) ω := h₂
    rw [h₁, h₂']
    unfold _root_.GD.N0232.N0720.N1214.d014261
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009244]
    ring
  rw [h1, integral_add (hφint.const_mul _) (hprod.const_mul _),
    integral_const_mul, integral_const_mul]
  congr 2
  rw [_root_.GD.N0232.N0720.N1198.d016717 m n g _ (_root_.GD.N0232.N0720.N1214.d014266 m n d)
    φ hφ.measurable]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 m n d,
    (_root_.GD.N0232.N0720.N1198.d016716 m n g φ hφ hφs).coeFn_toLp] with y h₁ h₂
  rw [h₁, h₂]




theorem d016722
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Continuous φ)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : Tendsto gSeq atTop (𝓝 g)) (y : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ y) atTop (𝓝 (_root_.GD.N0232.N0720.N1198.d016713 m n g φ y)) := by
  unfold _root_.GD.N0232.N0720.N1198.d016713
  have hact : Continuous (fun h : _root_.GD.N0232.N0720.N1025.d014301 ↦ h • y) := by
    have hpair : Continuous (fun h : _root_.GD.N0232.N0720.N1025.d014301 ↦
        ((h, y) : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n)) :=
      continuous_id.prodMk continuous_const
    have := (_root_.GD.N0232.N0720.N1198.d016708 m n).comp hpair
    exact this
  have hlik : Continuous (fun h : _root_.GD.N0232.N0720.N1025.d014301 ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 h⁻¹ _root_.GD.N0232.N0720.N1080.d014169) y) := by
    have hpair : Continuous (fun h : _root_.GD.N0232.N0720.N1025.d014301 ↦
        ((_root_.GD.N0232.N0720.N1215.d014272 h⁻¹ _root_.GD.N0232.N0720.N1080.d014169, y) : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1080.d014170 m n)) :=
      _root_.GD.N0232.N0720.N1199.d016699.prodMk continuous_const
    have := (_root_.GD.N0232.N0720.N1198.d016707 m n).comp hpair
    exact this
  exact (((hφ.comp hact).mul hlik).tendsto g).comp hg



theorem d016723
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Continuous φ) (hφs : HasCompactSupport φ)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : Tendsto gSeq atTop (𝓝 g)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j y, ‖_root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ y‖ ≤ B := by
  obtain ⟨Cφ, hCφ⟩ := hφ.bounded_above_of_compact_support hφs
  have hS : IsCompact (insert g (Set.range gSeq)) := hg.isCompact_insert_range
  have hinvact : Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1⁻¹ • p.2) := by
    have hpair : Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦
        ((p.1⁻¹, p.2) : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n)) :=
      (_root_.GD.N0232.N0720.N1199.d016698.comp continuous_fst).prodMk continuous_snd
    have := (_root_.GD.N0232.N0720.N1198.d016708 m n).comp hpair
    exact this
  have hK : IsCompact ((fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1⁻¹ • p.2) ''
      ((insert g (Set.range gSeq)) ×ˢ tsupport φ)) :=
    (hS.prod hφs).image hinvact
  have hS' : IsCompact ((fun h : _root_.GD.N0232.N0720.N1025.d014301 ↦ _root_.GD.N0232.N0720.N1215.d014272 h⁻¹ _root_.GD.N0232.N0720.N1080.d014169) ''
      insert g (Set.range gSeq)) :=
    hS.image _root_.GD.N0232.N0720.N1199.d016699
  obtain ⟨L, hL⟩ := (hS'.prod hK).exists_bound_of_continuousOn
    (_root_.GD.N0232.N0720.N1198.d016707 m n).continuousOn
  refine ⟨|Cφ| * |L|, by positivity, fun j y ↦ ?_⟩
  unfold _root_.GD.N0232.N0720.N1198.d016713
  by_cases hzero : φ (gSeq j • y) = 0
  · rw [hzero, zero_mul, norm_zero]
    positivity
  · have hmem : gSeq j • y ∈ tsupport φ := subset_tsupport φ hzero
    have hyK : y ∈ (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦ p.1⁻¹ • p.2) ''
        ((insert g (Set.range gSeq)) ×ˢ tsupport φ) := by
      refine ⟨(gSeq j, gSeq j • y), ⟨Set.mem_insert_of_mem _ ⟨j, rfl⟩, hmem⟩, ?_⟩
      exact _root_.GD.N0232.N0720.N1198.d016711 m n (gSeq j) y
    have hθ : _root_.GD.N0232.N0720.N1215.d014272 (gSeq j)⁻¹ _root_.GD.N0232.N0720.N1080.d014169 ∈
        (fun h : _root_.GD.N0232.N0720.N1025.d014301 ↦ _root_.GD.N0232.N0720.N1215.d014272 h⁻¹ _root_.GD.N0232.N0720.N1080.d014169) ''
          insert g (Set.range gSeq) :=
      ⟨gSeq j, Set.mem_insert_of_mem _ ⟨j, rfl⟩, rfl⟩
    have hℓ := hL (_root_.GD.N0232.N0720.N1215.d014272 (gSeq j)⁻¹ _root_.GD.N0232.N0720.N1080.d014169, y) ⟨hθ, hyK⟩
    rw [norm_mul]
    exact mul_le_mul ((hCφ _).trans (le_abs_self _)) (hℓ.trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)


theorem d016724
    (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Continuous φ) (hφs : HasCompactSupport φ)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : Tendsto gSeq atTop (𝓝 g)) :
    Tendsto (fun j ↦ (_root_.GD.N0232.N0720.N1198.d016716 m n (gSeq j) φ hφ hφs).toLp (_root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ))
      atTop (𝓝 ((_root_.GD.N0232.N0720.N1198.d016716 m n g φ hφ hφs).toLp (_root_.GD.N0232.N0720.N1198.d016713 m n g φ))) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  obtain ⟨B, hB, hbound⟩ := _root_.GD.N0232.N0720.N1198.d016723 m n φ hφ hφs gSeq g hg
  have hui : UnifIntegrable (fun j ↦ _root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    refine unifIntegrable_of one_le_two ENNReal.ofNat_ne_top
      (fun j ↦ (_root_.GD.N0232.N0720.N1198.d016714 m n (gSeq j) φ hφ).aestronglyMeasurable) ?_
    intro ε hε
    refine ⟨Real.toNNReal (B + 1), fun j ↦ ?_⟩
    have hzero : ({x | Real.toNNReal (B + 1) ≤ ‖_root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ x‖₊}).indicator
        (_root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ) = 0 := by
      funext x
      apply Set.indicator_of_notMem
      intro hx
      have h1 : (Real.toNNReal (B + 1) : ℝ) ≤ ‖_root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ x‖ := by
        have := NNReal.coe_le_coe.2 hx
        rwa [coe_nnnorm] at this
      rw [Real.coe_toNNReal _ (by positivity)] at h1
      linarith [hbound j x]
    rw [hzero, eLpNorm_zero]
    exact bot_le
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top
    (fun j ↦ (_root_.GD.N0232.N0720.N1198.d016714 m n (gSeq j) φ hφ).aestronglyMeasurable)
    (_root_.GD.N0232.N0720.N1198.d016716 m n g φ hφ hφs) hui
    (Eventually.of_forall fun y ↦ _root_.GD.N0232.N0720.N1198.d016722 m n φ hφ gSeq g hg y)




theorem d016725
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (v : H)
    (hu : Tendsto (fun j ↦ toWeakSpace ℝ H (u j)) atTop (𝓝 (toWeakSpace ℝ H v)))
    (w : H) :
    Tendsto (fun j ↦ ⟪w, u j⟫) atTop (𝓝 ⟪w, v⟫) := by
  have hc := WeakBilin.eval_continuous (topDualPairing ℝ H).flip
    (InnerProductSpace.toDual ℝ H w)
  have := (hc.tendsto (toWeakSpace ℝ H v)).comp hu
  exact this



theorem d016726 :
    Dense {Φ : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) |
      ∃ (φ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hφ : Continuous φ) (hφs : HasCompactSupport φ),
        Φ = (_root_.GD.N0232.N0720.N1198.d016718 m n φ hφ hφs).toLp φ} := by
  rw [Metric.dense_iff]
  intro Φ ε hε
  obtain ⟨φ, hφs, hdist, hφ, hφ2⟩ := (Lp.memLp Φ).exists_hasCompactSupport_eLpNorm_sub_le
    (p := 2) ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 2))
    (by simp [hε])
  refine ⟨(_root_.GD.N0232.N0720.N1198.d016718 m n φ hφ hφs).toLp φ, ?_, φ, hφ, hφs, rfl⟩
  rw [Metric.mem_ball, Lp.dist_def]
  have h1 : eLpNorm (⇑((_root_.GD.N0232.N0720.N1198.d016718 m n φ hφ hφs).toLp φ) - ⇑Φ) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)
      = eLpNorm (⇑Φ - φ) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    rw [← eLpNorm_neg, neg_sub]
    apply eLpNorm_congr_ae
    filter_upwards [(_root_.GD.N0232.N0720.N1198.d016718 m n φ hφ hφs).coeFn_toLp] with x hx
    simp [hx]
  rw [h1]
  calc (eLpNorm (⇑Φ - φ) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)).toReal
      ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
    _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < ε := by linarith



theorem d016727 (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g =
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2 := rfl




theorem d016728
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : Tendsto gSeq atTop (𝓝 g))
    (qSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : Tendsto qSeq atTop (𝓝 q)) :
    _root_.GD.N0230.N0708.d001170 ℝ (fun j ↦ _root_.GD.N0232.N0720.N1199.d016686 m n hm hn (qSeq j) (gSeq j)) atTop
      (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g) := by

  set dSeq : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm (qSeq j)).1 with hdSeq
  set d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1 with hd
  have hdweak : Tendsto (fun j ↦ toWeakSpace ℝ _ (dSeq j)) atTop (𝓝 (toWeakSpace ℝ _ d)) := by
    have := (continuous_subtype_val.tendsto q).comp hq
    have hval : ∀ p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
        p.1 = toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1 := by
      intro p
      rw [_root_.GD.N0232.N0720.N1025.d014309]
      simp
    simpa only [Function.comp_def, hval] using this
  have hdinner : ∀ w, Tendsto (fun j ↦ ⟪w, dSeq j⟫) atTop (𝓝 ⟪w, d⟫) :=
    _root_.GD.N0232.N0720.N1198.d016725 dSeq d hdweak
  have hdbound : ∀ j, ‖dSeq j‖ ≤ _root_.GD.N0232.N0720.N1080.d014248 m n hm hn := fun j ↦
    _root_.GD.N0232.N0720.N1080.d014250 m n hm hn _
      ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm (qSeq j)).2
  apply _root_.GD.N0230.N0570.d001187
  intro w

  have hmain := _root_.GD.N0232.N0720.N1198.d016704
    (fun j ↦ _root_.GD.N0232.N0720.N1199.d016686 m n hm hn (qSeq j) (gSeq j)) (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g)
    (_root_.GD.N0232.N0720.N1080.d014248 m n hm hn)
    (fun j ↦ _root_.GD.N0232.N0720.N1199.d016688 m n hm hn (qSeq j) (gSeq j))
    (_root_.GD.N0232.N0720.N1199.d016688 m n hm hn q g)
    _ (_root_.GD.N0232.N0720.N1198.d016726 m n) ?_ w
  · simpa only [real_inner_comm] using hmain
  rintro Φ ⟨φ, hφ, hφs, rfl⟩
  simp only [_root_.GD.N0232.N0720.N1198.d016727]
  rw [_root_.GD.N0232.N0720.N1198.d016721 m n hm hn g _ _ φ hφ hφs]
  refine (tendsto_congr fun j ↦
    _root_.GD.N0232.N0720.N1198.d016721 m n hm hn (gSeq j) _ _ φ hφ hφs).2 ?_
  have hshift : Tendsto (fun j ↦ (gSeq j).shift) atTop (𝓝 g.shift) :=
    (_root_.GD.N0232.N0719.N0945.d009267.tendsto g).comp hg
  have hdil : Tendsto (fun j ↦ (gSeq j).d009239) atTop (𝓝 g.d009239) :=
    (_root_.GD.N0232.N0719.N0945.d009268.tendsto g).comp hg
  have hprobe := _root_.GD.N0232.N0720.N1198.d016724 m n φ hφ hφs gSeq g hg

  have hpair : Tendsto (fun j ↦ ⟪dSeq j,
      (_root_.GD.N0232.N0720.N1198.d016716 m n (gSeq j) φ hφ hφs).toLp (_root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ)⟫) atTop
      (𝓝 ⟪d, (_root_.GD.N0232.N0720.N1198.d016716 m n g φ hφ hφs).toLp (_root_.GD.N0232.N0720.N1198.d016713 m n g φ)⟫) := by
    set Ψ : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
      fun j ↦ (_root_.GD.N0232.N0720.N1198.d016716 m n (gSeq j) φ hφ hφs).toLp (_root_.GD.N0232.N0720.N1198.d016713 m n (gSeq j) φ) with hΨ
    set Ψlim : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
      (_root_.GD.N0232.N0720.N1198.d016716 m n g φ hφ hφs).toLp (_root_.GD.N0232.N0720.N1198.d016713 m n g φ) with hΨlim
    have hsplit : ∀ j, ⟪dSeq j, Ψ j⟫ = ⟪dSeq j, Ψ j - Ψlim⟫ + ⟪Ψlim, dSeq j⟫ := by
      intro j
      rw [inner_sub_right, real_inner_comm Ψlim]
      ring
    have hfun : (fun j ↦ ⟪dSeq j, Ψ j⟫) =
        fun j ↦ ⟪dSeq j, Ψ j - Ψlim⟫ + ⟪Ψlim, dSeq j⟫ := funext hsplit
    rw [hfun]
    have h1 : Tendsto (fun j ↦ ⟪dSeq j, Ψ j - Ψlim⟫) atTop (𝓝 0) := by
      have hnorm : Tendsto (fun j ↦ ‖Ψ j - Ψlim‖) atTop (𝓝 0) := by
        rw [← tendsto_sub_nhds_zero_iff] at hprobe
        exact (tendsto_zero_iff_norm_tendsto_zero).1 hprobe
      have hbd : ∀ j, |⟪dSeq j, Ψ j - Ψlim⟫| ≤
          _root_.GD.N0232.N0720.N1080.d014248 m n hm hn * ‖Ψ j - Ψlim‖ := fun j ↦
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hdbound j) (norm_nonneg _))
      have hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1080.d014248 m n hm hn * ‖Ψ j - Ψlim‖) atTop
          (𝓝 (_root_.GD.N0232.N0720.N1080.d014248 m n hm hn * 0)) := hnorm.const_mul _
      rw [mul_zero] at hR
      exact squeeze_zero_norm hbd hR
    have h2 := hdinner Ψlim
    have := h1.add h2
    rw [zero_add] at this
    rwa [real_inner_comm d Ψlim] at this
  exact (hshift.mul tendsto_const_nhds).add (hdil.mul hpair)


theorem d016729
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : Tendsto gSeq atTop (𝓝 g))
    (qSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : Tendsto qSeq atTop (𝓝 q)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1025.d014316 m n hm hn (gSeq j) (qSeq j)) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q)) := by
  rw [tendsto_subtype_rng]
  have hweak := _root_.GD.N0232.N0720.N1198.d016728 m n hm hn gSeq g hg qSeq q hq
  unfold _root_.GD.N0230.N0708.d001170 at hweak
  have hval : ∀ (h : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn),
      (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn h p).1 =
        toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn p h) := by
    intro h p
    rw [_root_.GD.N0232.N0720.N1199.d016686, _root_.GD.N0232.N0720.N1025.d014309]
    simp
  simpa only [hval] using hweak




theorem d016730 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ↦
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn p.1 p.2) := by
  rw [continuous_iff_seqContinuous]
  intro pSeq p hp
  rw [Prod.tendsto_iff] at hp
  exact _root_.GD.N0232.N0720.N1198.d016729 m n hm hn (fun j ↦ (pSeq j).1) p.1 hp.1
    (fun j ↦ (pSeq j).2) p.2 hp.2



theorem d016731 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1025.d014301 × _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ↦
      _root_.GD.N0232.N0720.N1261.d014945 m n hm hn p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1261.d014945
  exact (continuous_dist.comp
    ((_root_.GD.N0232.N0720.N1198.d016730 m n hm hn).prodMk continuous_snd)).pow 2




theorem d016732 (S : Set _root_.GD.N0232.N0720.N1025.d014301) :
    IsClosed {p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn | ∀ g ∈ S, _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p} := by
  have : {p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn | ∀ g ∈ S, _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p} =
      ⋂ g ∈ S, {p | _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p} := by
    ext p
    simp
  rw [this]
  refine isClosed_biInter fun g _ ↦ ?_
  exact isClosed_eq (_root_.GD.N0232.N0720.N1483.d014904 m n hm hn g) continuous_id

end

end N1198
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1198.d016730
#print axioms _root_.GD.N0232.N0720.N1198.d016729
#print axioms _root_.GD.N0232.N0720.N1198.d016721
#print axioms _root_.GD.N0232.N0720.N1198.d016731
#print axioms _root_.GD.N0232.N0720.N1198.d016724
