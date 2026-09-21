import GD.Module0727



























open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0841

noncomputable section



section CountableRepair

variable {G X Y : Type*}
  [Group G] [Countable G]
  [MulAction G X] [MulAction G Y]
  [MeasurableSpace X] [MeasurableSpace Y]



def d011010 (G : Type*)
    [Group G] [MulAction G X] [MulAction G Y]
    (d : X → Y) : Set X :=
  {x | ∀ g : G, d (g • x) = g • d x}

@[simp]
theorem d011011
    (d : X → Y) (x : X) :
    x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d ↔
      ∀ g : G, d (g • x) = g • d x :=
  Iff.rfl



theorem d011012
    (d : X → Y) (g : G) (x : X) :
    x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d →
      g • x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d := by
  intro hx h
  calc
    d (h • (g • x)) = d ((h * g) • x) := by rw [mul_smul]
    _ = (h * g) • d x := hx (h * g)
    _ = h • (g • d x) := by rw [mul_smul]
    _ = h • d (g • x) := by rw [hx g]


theorem d011013
    (d : X → Y) (g : G) (x : X) :
    g • x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d ↔
      x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d := by
  constructor
  · intro hg
    have hback := _root_.GD.N0232.N0719.N0841.d011012 d g⁻¹ (g • x) hg
    simpa using hback
  · exact _root_.GD.N0232.N0719.N0841.d011012 d g x



theorem d011014
    (μ : Measure X) (d : X → Y)
    (hperArrow : ∀ g : G,
      (fun x => d (g • x)) =ᵐ[μ] (fun x => g • d x)) :
    ∀ᵐ x ∂μ, x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d := by
  apply ae_all_iff.2
  intro g
  exact hperArrow g




theorem d011015
    [MeasurableEq Y]
    (d : X → Y) (hd : Measurable d)
    (hsource : ∀ g : G, Measurable (fun x : X => g • x))
    (htarget : ∀ g : G, Measurable (fun y : Y => g • y)) :
    MeasurableSet (_root_.GD.N0232.N0719.N0841.d011010 G d) := by
  have hset : _root_.GD.N0232.N0719.N0841.d011010 G d =
      ⋂ g : G, {x : X | d (g • x) = g • d x} := by
    ext x
    simp [_root_.GD.N0232.N0719.N0841.d011010]
  rw [hset]
  apply MeasurableSet.iInter
  intro g
  exact measurableSet_eq_fun
    (hd.comp (hsource g)) ((htarget g).comp hd)



def d011016 (G : Type*)
    [Group G] [MulAction G X] [MulAction G Y]
    (d fallback : X → Y) : X → Y := by
  classical
  exact (_root_.GD.N0232.N0719.N0841.d011010 G d).piecewise d fallback

theorem d011017
    (d fallback : X → Y)
    (hset : MeasurableSet (_root_.GD.N0232.N0719.N0841.d011010 G d))
    (hd : Measurable d) (hfallback : Measurable fallback) :
    Measurable (_root_.GD.N0232.N0719.N0841.d011016 G d fallback) := by
  classical
  exact hd.piecewise hset hfallback



theorem d011018
    (μ : Measure X) (d fallback : X → Y)
    (hperArrow : ∀ g : G,
      (fun x => d (g • x)) =ᵐ[μ] (fun x => g • d x)) :
    _root_.GD.N0232.N0719.N0841.d011016 G d fallback =ᵐ[μ] d := by
  classical
  filter_upwards [_root_.GD.N0232.N0719.N0841.d011014 μ d hperArrow] with x hx
  simp [_root_.GD.N0232.N0719.N0841.d011016, hx]




theorem d011019
    (d fallback : X → Y)
    (hfallback : ∀ g : G, ∀ x : X,
      fallback (g • x) = g • fallback x) :
    ∀ g : G, ∀ x : X,
      _root_.GD.N0232.N0719.N0841.d011016 G d fallback (g • x) =
        g • _root_.GD.N0232.N0719.N0841.d011016 G d fallback x := by
  classical
  intro g x
  by_cases hx : x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d
  · have hgx : g • x ∈ _root_.GD.N0232.N0719.N0841.d011010 G d :=
      (_root_.GD.N0232.N0719.N0841.d011013 d g x).2 hx
    simp [_root_.GD.N0232.N0719.N0841.d011016, hx, hgx, hx g]
  · have hgx : g • x ∉ _root_.GD.N0232.N0719.N0841.d011010 G d := by
      simpa [_root_.GD.N0232.N0719.N0841.d011013 d g x] using hx
    simp [_root_.GD.N0232.N0719.N0841.d011016, hx, hgx, hfallback g x]





theorem d011020
    [MeasurableEq Y]
    (μ : Measure X) (d fallback : X → Y)
    (hd : Measurable d) (hfallback_meas : Measurable fallback)
    (hsource : ∀ g : G, Measurable (fun x : X => g • x))
    (htarget : ∀ g : G, Measurable (fun y : Y => g • y))
    (hperArrow : ∀ g : G,
      (fun x => d (g • x)) =ᵐ[μ] (fun x => g • d x))
    (hfallback : ∀ g : G, ∀ x : X,
      fallback (g • x) = g • fallback x) :
    ∃ d' : X → Y,
      Measurable d' ∧
      d' =ᵐ[μ] d ∧
      ∀ g : G, ∀ x : X, d' (g • x) = g • d' x := by
  refine ⟨_root_.GD.N0232.N0719.N0841.d011016 G d fallback, ?_, ?_, ?_⟩
  · exact _root_.GD.N0232.N0719.N0841.d011017 d fallback
      (_root_.GD.N0232.N0719.N0841.d011015 d hd hsource htarget)
      hd hfallback_meas
  · exact _root_.GD.N0232.N0719.N0841.d011018 μ d fallback hperArrow
  · exact _root_.GD.N0232.N0719.N0841.d011019 d fallback hfallback

end CountableRepair



open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0107

variable (k : ℕ) (sizes : Fin k → ℕ)



theorem d011021
    (shift dilation : ℝ) :
    Continuous (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation) := by
  unfold _root_.GD.N0232.N0719.N0900.d009095 _root_.GD.N0107.d009018
  fun_prop



theorem d011022
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    Continuous (fun p : ℝ × ℝ =>
      _root_.GD.N0232.N0719.N0900.d009095 k sizes p.1 p.2 omega) := by
  unfold _root_.GD.N0232.N0719.N0900.d009095 _root_.GD.N0107.d009018
  fun_prop




theorem d011023
    (μ : Measure (_root_.GD.N0232.N0719.d009173 k sizes))
    [μ.IsOpenPosMeasure]
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Continuous d)
    (hperArrow : ∀ shift dilation : ℚ, 0 < dilation →
      (fun omega =>
          d (_root_.GD.N0232.N0719.N0900.d009095 k sizes (shift : ℝ) (dilation : ℝ) omega))
        =ᵐ[μ]
      (fun omega => (shift : ℝ) + (dilation : ℝ) * d omega)) :
    ∀ shift dilation : ℚ, 0 < dilation → ∀ omega,
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes (shift : ℝ) (dilation : ℝ) omega) =
        (shift : ℝ) + (dilation : ℝ) * d omega := by
  intro shift dilation hdilation
  have hleft : Continuous (fun omega =>
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes (shift : ℝ) (dilation : ℝ) omega)) :=
    hd.comp (_root_.GD.N0232.N0719.N0841.d011021 k sizes _ _)
  have hright : Continuous (fun omega : _root_.GD.N0232.N0719.d009173 k sizes =>
      (shift : ℝ) + (dilation : ℝ) * d omega) := by
    fun_prop
  exact congrFun
    ((hleft.ae_eq_iff_eq μ hright).1
      (hperArrow shift dilation hdilation))




theorem d011024
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Continuous d)
    (hrational : ∀ shift dilation : ℚ, 0 < dilation → ∀ omega,
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes (shift : ℝ) (dilation : ℝ) omega) =
        (shift : ℝ) + (dilation : ℝ) * d omega) :
    ∀ shift dilation : ℝ, 0 < dilation → ∀ omega,
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
        shift + dilation * d omega := by
  have htranslation : ∀ shift : ℝ, ∀ omega,
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift 1 omega) = shift + d omega := by
    intro shift omega
    refine Rat.denseRange_cast.induction_on shift ?_ ?_
    · exact isClosed_eq
        (hd.comp (by
          have h := _root_.GD.N0232.N0719.N0841.d011022 k sizes omega
          exact h.comp (continuous_id.prodMk continuous_const)))
        (by fun_prop)
    · intro q
      simpa using hrational q 1 (by norm_num) omega
  have hscale : ∀ dilation : ℝ, 0 < dilation → ∀ omega,
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 dilation omega) =
        dilation * d omega := by
    intro dilation hdilation omega
    let S : Set ℝ := {scale |
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 scale omega) = scale * d omega}
    have hSclosed : IsClosed S := by
      exact isClosed_eq
        (hd.comp (by
          have h := _root_.GD.N0232.N0719.N0841.d011022 k sizes omega
          exact h.comp (continuous_const.prodMk continuous_id)))
        (by fun_prop)
    obtain ⟨u, _hu_mono, hu_mem, hu_tendsto⟩ :=
      Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
        Rat.cast_strictMono.monotone hdilation
    apply hSclosed.mem_of_tendsto hu_tendsto
    filter_upwards [] with n
    have hu_pos : 0 < u n := by
      exact_mod_cast (hu_mem n).1
    simpa [S] using hrational 0 (u n) hu_pos omega
  intro shift dilation hdilation omega
  have hcompose :
      _root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega =
        _root_.GD.N0232.N0719.N0900.d009095 k sizes shift 1
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 dilation omega) := by
    ext i j
    simp [_root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018]
  rw [hcompose, htranslation shift,
    hscale dilation hdilation omega]




theorem d011025
    (μ : Measure (_root_.GD.N0232.N0719.d009173 k sizes))
    [μ.IsOpenPosMeasure]
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Continuous d)
    (hperArrow : ∀ shift dilation : ℚ, 0 < dilation →
      (fun omega =>
          d (_root_.GD.N0232.N0719.N0900.d009095 k sizes (shift : ℝ) (dilation : ℝ) omega))
        =ᵐ[μ]
      (fun omega => (shift : ℝ) + (dilation : ℝ) * d omega)) :
    ∀ shift dilation : ℝ, 0 < dilation → ∀ omega,
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
        shift + dilation * d omega := by
  apply _root_.GD.N0232.N0719.N0841.d011024 k sizes d hd
  exact _root_.GD.N0232.N0719.N0841.d011023
    k sizes μ d hd hperArrow

end

end N0841
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0841.d011019
#print axioms _root_.GD.N0232.N0719.N0841.d011025
