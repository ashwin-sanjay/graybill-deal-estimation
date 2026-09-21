import GD.Module1047






































open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Topology

namespace GD
namespace N0232
namespace N0720
namespace N1418

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1198
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608






theorem d017024
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r v w : H) (δ t : ℝ) (hδ : 0 ≤ δ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmargin : ‖r + v‖ ^ 2 ≤ ‖r‖ ^ 2 - δ * ‖v‖ ^ 2)
    (hperturb : ‖w‖ ^ 2 ≤ (1 - t) * δ * ‖v‖ ^ 2) :
    ‖r + w + t • v‖ ^ 2 ≤
      ‖r + w‖ ^ 2 -
        t * (Real.sqrt (1 - t) - Real.sqrt δ) ^ 2 * ‖v‖ ^ 2 := by
  set A := Real.sqrt (1 - t) with hA
  set B := Real.sqrt δ with hB
  have ht1' : 0 ≤ 1 - t := by linarith
  have hAsq : A ^ 2 = 1 - t := Real.sq_sqrt ht1'
  have hBsq : B ^ 2 = δ := Real.sq_sqrt hδ
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _

  have hrv : 2 * ⟪r, v⟫ ≤ -(1 + δ) * ‖v‖ ^ 2 := by
    have hexp := norm_add_sq_real r v
    nlinarith [hexp, hmargin]

  have hwnorm : ‖w‖ ≤ A * B * ‖v‖ := by
    have h1 : ‖w‖ ^ 2 ≤ (A * B * ‖v‖) ^ 2 := by
      have : (A * B * ‖v‖) ^ 2 = (1 - t) * δ * ‖v‖ ^ 2 := by
        rw [mul_pow, mul_pow, hAsq, hBsq]
      linarith [hperturb, this]
    have h2 : 0 ≤ A * B * ‖v‖ := by positivity
    nlinarith [norm_nonneg w, h1, h2]
  have hwv : 2 * ⟪w, v⟫ ≤ 2 * (A * B) * ‖v‖ ^ 2 := by
    have h1 : ⟪w, v⟫ ≤ ‖w‖ * ‖v‖ := real_inner_le_norm w v
    nlinarith [h1, hwnorm, norm_nonneg v]

  have hexpand : ‖r + w + t • v‖ ^ 2 =
      ‖r + w‖ ^ 2 + 2 * t * (⟪r, v⟫ + ⟪w, v⟫) + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real (r + w) (t • v), inner_smul_right, inner_add_left,
      norm_smul]
    simp only [Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  rw [hexpand]
  have hkey : -(1 + δ) + 2 * (A * B) + t = -(A - B) ^ 2 := by
    have : (1 : ℝ) + δ = (1 - t) + δ + t := by ring
    rw [this, ← hAsq, ← hBsq]
    ring
  have h1 : t * (2 * ⟪r, v⟫) ≤ t * (-(1 + δ) * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hrv ht0.le
  have h2 : t * (2 * ⟪w, v⟫) ≤ t * (2 * (A * B) * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hwv ht0.le
  have hkey' : t * (-(1 + δ) * ‖v‖ ^ 2) + t * (2 * (A * B) * ‖v‖ ^ 2) +
      t ^ 2 * ‖v‖ ^ 2 = -(t * (A - B) ^ 2 * ‖v‖ ^ 2) := by
    linear_combination (t * ‖v‖ ^ 2) * hkey
  linarith [h1, h2, hkey']



variable (m n : ℕ)

instance d017025 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance



theorem d017026 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014171 m n theta ≪ _root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [_root_.GD.N0232.N0720.N1499.d015006]
  exact withDensity_absolutelyContinuous _ _


def d017027 (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun ω ↦ d ω - theta.location

theorem d017028
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    AEStronglyMeasurable (_root_.GD.N0232.N0720.N1418.d017027 m n theta d) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
  ((Lp.aestronglyMeasurable d).mono_ac
    (_root_.GD.N0232.N0720.N1418.d017026 m n theta)).sub aestronglyMeasurable_const


theorem d017029
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta d =
      ∫⁻ ω, ENNReal.ofReal (_root_.GD.N0232.N0720.N1418.d017027 m n theta d ω ^ 2)
        ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := rfl



theorem d017030
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤) :
    MemLp (_root_.GD.N0232.N0720.N1418.d017027 m n theta d) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  apply (memLp_two_iff_integrable_sq
    (_root_.GD.N0232.N0720.N1418.d017028 m n theta d)).2
  have hlin : (∫⁻ ω, ENNReal.ofReal (_root_.GD.N0232.N0720.N1418.d017027 m n theta d ω ^ 2)
      ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) ≠ ⊤ := by
    rw [← _root_.GD.N0232.N0720.N1418.d017029]
    exact hfin
  have hint := integrable_toReal_of_lintegral_ne_top
    ((_root_.GD.N0232.N0720.N1418.d017028 m n theta d).aemeasurable.pow_const
      2).ennreal_ofReal hlin
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint


theorem d017031
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta d).toReal =
      ∫ ω, _root_.GD.N0232.N0720.N1418.d017027 m n theta d ω ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hint : Integrable (fun ω ↦ _root_.GD.N0232.N0720.N1418.d017027 m n theta d ω ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    (_root_.GD.N0232.N0720.N1418.d017030 m n theta d hfin).integrable_sq
  rw [_root_.GD.N0232.N0720.N1418.d017029,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ω ↦ sq_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ sq_nonneg _)]



theorem d017032
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hmem : MemLp (_root_.GD.N0232.N0720.N1418.d017027 m n theta d) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤ := by
  rw [_root_.GD.N0232.N0720.N1418.d017029,
    ← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
      (Eventually.of_forall fun ω ↦ sq_nonneg _)]
  exact ENNReal.ofReal_ne_top



theorem d017033
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (u : Lp ℝ 2 ν) (f : α → ℝ) (h : (u : α → ℝ) =ᵐ[ν] f) :
    ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq,
    _root_.GD.N0232.N0720.N1198.d016719]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx, sq]






theorem d017034
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤) (he : _root_.GD.N0232.N0720.N1080.d014182 m n theta e ≠ ⊤) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal =
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal +
        2 * ∫ ω, _root_.GD.N0232.N0720.N1418.d017027 m n theta p ω * (e ω - p ω) ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) +
        ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  set lam := _root_.GD.N0232.N0720.N1080.d014171 m n theta with hlam
  have hpmem := _root_.GD.N0232.N0720.N1418.d017030 m n theta p hp
  have hemem := _root_.GD.N0232.N0720.N1418.d017030 m n theta e he
  have hvmem : MemLp (fun ω ↦ e ω - p ω) 2 lam := by
    have := hemem.sub hpmem
    simpa [_root_.GD.N0232.N0720.N1418.d017027, Pi.sub_def, sub_sub_sub_cancel_right] using this
  set R := hpmem.toLp _ with hRdef
  set V := hvmem.toLp _ with hVdef
  have hR : ‖R‖ ^ 2 = (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal := by
    rw [_root_.GD.N0232.N0720.N1418.d017033 R _ hpmem.coeFn_toLp,
      _root_.GD.N0232.N0720.N1418.d017031 m n theta p hp]
  have hV : ‖V‖ ^ 2 = ∫ ω, (e ω - p ω) ^ 2 ∂lam :=
    _root_.GD.N0232.N0720.N1418.d017033 V _ hvmem.coeFn_toLp
  have hRV : ‖R + V‖ ^ 2 = (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal := by
    rw [_root_.GD.N0232.N0720.N1418.d017031 m n theta e he]
    apply _root_.GD.N0232.N0720.N1418.d017033
    filter_upwards [Lp.coeFn_add R V, hpmem.coeFn_toLp, hvmem.coeFn_toLp]
      with ω h₁ h₂ h₃
    rw [h₁]
    simp only [Pi.add_apply]
    rw [h₂, h₃]
    unfold _root_.GD.N0232.N0720.N1418.d017027
    ring
  have hinner : ⟪R, V⟫ =
      ∫ ω, _root_.GD.N0232.N0720.N1418.d017027 m n theta p ω * (e ω - p ω) ∂lam := by
    rw [_root_.GD.N0232.N0720.N1198.d016719]
    apply integral_congr_ae
    filter_upwards [hpmem.coeFn_toLp, hvmem.coeFn_toLp] with ω h₁ h₂
    rw [h₁, h₂]
  have hexp := norm_add_sq_real R V
  rw [hRV, hR, hV, hinner] at hexp
  linarith



theorem d017035
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤) (he : _root_.GD.N0232.N0720.N1080.d014182 m n theta e ≠ ⊤) (δ : ℝ) :
    ((_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal -
          δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) ↔
      2 * ∫ ω, _root_.GD.N0232.N0720.N1418.d017027 m n theta p ω * (e ω - p ω) ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) ≤
        -(1 + δ) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  rw [_root_.GD.N0232.N0720.N1418.d017034 m n theta p e hp he]
  constructor <;> intro h <;> linarith






theorem d017036
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤) (hq : _root_.GD.N0232.N0720.N1080.d014182 m n theta q ≠ ⊤)
    (he : _root_.GD.N0232.N0720.N1080.d014182 m n theta e ≠ ⊤)
    (δ t : ℝ) (hδ : 0 ≤ δ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmargin : (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal -
        δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta))
    (hperturb : (∫ ω, (q ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) ≤
      (1 - t) * δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (q + t • (e - p))).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta q).toReal -
          t * (Real.sqrt (1 - t) - Real.sqrt δ) ^ 2 *
            ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) ∧
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (q + t • (e - p)) ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta q := by
  set lam := _root_.GD.N0232.N0720.N1080.d014171 m n theta with hlam
  have hpmem := _root_.GD.N0232.N0720.N1418.d017030 m n theta p hp
  have hqmem := _root_.GD.N0232.N0720.N1418.d017030 m n theta q hq
  have hemem := _root_.GD.N0232.N0720.N1418.d017030 m n theta e he
  have hvmem : MemLp (fun ω ↦ e ω - p ω) 2 lam := by
    have := hemem.sub hpmem
    simpa [_root_.GD.N0232.N0720.N1418.d017027, Pi.sub_def, sub_sub_sub_cancel_right] using this
  have hwmem : MemLp (fun ω ↦ q ω - p ω) 2 lam := by
    have := hqmem.sub hpmem
    simpa [_root_.GD.N0232.N0720.N1418.d017027, Pi.sub_def, sub_sub_sub_cancel_right] using this
  set R := hpmem.toLp _ with hRdef
  set V := hvmem.toLp _ with hVdef
  set W := hwmem.toLp _ with hWdef
  have hR : ‖R‖ ^ 2 = (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal := by
    rw [_root_.GD.N0232.N0720.N1418.d017033 R _ hpmem.coeFn_toLp,
      _root_.GD.N0232.N0720.N1418.d017031 m n theta p hp]
  have hV : ‖V‖ ^ 2 = ∫ ω, (e ω - p ω) ^ 2 ∂lam :=
    _root_.GD.N0232.N0720.N1418.d017033 V _ hvmem.coeFn_toLp
  have hW : ‖W‖ ^ 2 = ∫ ω, (q ω - p ω) ^ 2 ∂lam :=
    _root_.GD.N0232.N0720.N1418.d017033 W _ hwmem.coeFn_toLp
  have hRV : ‖R + V‖ ^ 2 = (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal := by
    rw [_root_.GD.N0232.N0720.N1418.d017031 m n theta e he]
    apply _root_.GD.N0232.N0720.N1418.d017033
    filter_upwards [Lp.coeFn_add R V, hpmem.coeFn_toLp, hvmem.coeFn_toLp]
      with ω h₁ h₂ h₃
    rw [h₁]
    simp only [Pi.add_apply]
    rw [h₂, h₃]
    unfold _root_.GD.N0232.N0720.N1418.d017027
    ring
  have hRW : ‖R + W‖ ^ 2 = (_root_.GD.N0232.N0720.N1080.d014182 m n theta q).toReal := by
    rw [_root_.GD.N0232.N0720.N1418.d017031 m n theta q hq]
    apply _root_.GD.N0232.N0720.N1418.d017033
    filter_upwards [Lp.coeFn_add R W, hpmem.coeFn_toLp, hwmem.coeFn_toLp]
      with ω h₁ h₂ h₃
    rw [h₁]
    simp only [Pi.add_apply]
    rw [h₂, h₃]
    unfold _root_.GD.N0232.N0720.N1418.d017027
    ring

  have hcomp_ref : ((q + t • (e - p) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
      _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun ω ↦ q ω + t * (e ω - p ω) := by
    filter_upwards [Lp.coeFn_add q (t • (e - p)),
      Lp.coeFn_smul t (e - p), Lp.coeFn_sub e p] with ω h₁ h₂ h₃
    rw [h₁]
    simp only [Pi.add_apply]
    rw [h₂]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h₃]
    simp [Pi.sub_apply]
  have hcomp_lam : ((q + t • (e - p) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
      _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) =ᵐ[lam] fun ω ↦ q ω + t * (e ω - p ω) :=
    (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le hcomp_ref
  have hcompres : _root_.GD.N0232.N0720.N1418.d017027 m n theta (q + t • (e - p)) =ᵐ[lam]
      fun ω ↦ _root_.GD.N0232.N0720.N1418.d017027 m n theta q ω + t * (e ω - p ω) := by
    filter_upwards [hcomp_lam] with ω hω
    unfold _root_.GD.N0232.N0720.N1418.d017027
    rw [hω]
    ring
  have hcompmem : MemLp (_root_.GD.N0232.N0720.N1418.d017027 m n theta (q + t • (e - p))) 2 lam := by
    apply MemLp.ae_eq hcompres.symm
    exact hqmem.add (hvmem.const_mul t)
  have hcompfin : _root_.GD.N0232.N0720.N1080.d014182 m n theta (q + t • (e - p)) ≠ ⊤ :=
    _root_.GD.N0232.N0720.N1418.d017032 m n theta _ hcompmem
  have hRWtV : ‖R + W + t • V‖ ^ 2 =
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta (q + t • (e - p))).toReal := by
    rw [_root_.GD.N0232.N0720.N1418.d017031 m n theta _ hcompfin]
    apply _root_.GD.N0232.N0720.N1418.d017033
    have h₄ := hcompres
    filter_upwards [Lp.coeFn_add (R + W) (t • V), Lp.coeFn_add R W,
      Lp.coeFn_smul t V, hpmem.coeFn_toLp, hvmem.coeFn_toLp,
      hwmem.coeFn_toLp, h₄] with ω h₁ h₂ h₃ hp' hv' hw' hres
    rw [h₁]
    simp only [Pi.add_apply]
    rw [h₂]
    simp only [Pi.add_apply]
    rw [h₃]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hp', hv', hw', hres]
    unfold _root_.GD.N0232.N0720.N1418.d017027
    ring
  have happly := _root_.GD.N0232.N0720.N1418.d017024 R V W δ t hδ ht0 ht1
    (by rw [hRV, hR, hV]; exact hmargin)
    (by rw [hW, hV]; exact hperturb)
  rw [hRWtV, hRW, hV] at happly
  have hdeficit : 0 ≤ t * (Real.sqrt (1 - t) - Real.sqrt δ) ^ 2 *
      ∫ ω, (e ω - p ω) ^ 2 ∂lam := by
    have : (0 : ℝ) ≤ ∫ ω, (e ω - p ω) ^ 2 ∂lam :=
      integral_nonneg fun ω ↦ sq_nonneg _
    positivity
  refine ⟨happly, (ENNReal.toReal_le_toReal hcompfin hq).1 (by linarith)⟩




theorem d017037
    (p q e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (he : _root_.GD.N0232.N0720.N1159.d014637 m n e)
    (δ t : ℝ) (hδ : 0 ≤ δ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmargin : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal -
        δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta))
    (hperturb : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      (∫ ω, (q ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) ≤
        (1 - t) * δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (q + t • (e - p)) q := by
  intro theta
  exact (_root_.GD.N0232.N0720.N1418.d017036 m n theta p q e (hp theta) (hq theta) (he theta)
    δ t hδ ht0 ht1 (hmargin theta) (hperturb theta)).2


theorem d017038
    (p q e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (t : ℝ)
    (ht0 : 0 < t) (hne : e ≠ p) :
    q + t • (e - p) ≠ q := by
  intro hcontra
  apply hne
  have h1 : t • (e - p) = 0 := by
    have := congrArg (fun x ↦ x - q) hcontra
    simpa [add_sub_cancel_left] using this
  rcases smul_eq_zero.1 h1 with h | h
  · exact absurd h ht0.ne'
  · exact sub_eq_zero.1 h



theorem d017039
    (p q e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (he : _root_.GD.N0232.N0720.N1159.d014637 m n e) (hne : e ≠ p)
    (δ t : ℝ) (hδ : 0 ≤ δ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmargin : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal -
        δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta))
    (hperturb : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      (∫ ω, (q ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) ≤
        (1 - t) * δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    ¬ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) q := by
  intro hterm
  exact _root_.GD.N0232.N0720.N1418.d017038 m n p q e t ht0 hne
    (hterm _ (_root_.GD.N0232.N0720.N1418.d017037 m n p q e hp hq he
      δ t hδ ht0 ht1 hmargin hperturb))






theorem d017040
    (p q e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (he : _root_.GD.N0232.N0720.N1159.d014637 m n e) (hne : e ≠ p)
    (δ t : ℝ) (hδ : 0 ≤ δ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmargin : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal -
        δ * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta))
    (hterm : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) q) :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      (1 - t) * δ * (∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) <
        ∫ ω, (q ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  by_contra hcontra
  refine _root_.GD.N0232.N0720.N1418.d017039 m n p q e hp hq he hne
    δ t hδ ht0 ht1 hmargin ?_ hterm
  intro theta
  by_contra hlt
  exact hcontra ⟨theta, lt_of_not_ge hlt⟩

end

end N1418
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1418.d017024
#print axioms _root_.GD.N0232.N0720.N1418.d017036
#print axioms _root_.GD.N0232.N0720.N1418.d017034
#print axioms _root_.GD.N0232.N0720.N1418.d017035
#print axioms _root_.GD.N0232.N0720.N1418.d017037
#print axioms _root_.GD.N0232.N0720.N1418.d017039
#print axioms _root_.GD.N0232.N0720.N1418.d017040
