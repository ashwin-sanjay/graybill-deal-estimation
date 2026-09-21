import GD.Module0041
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
















namespace GD
namespace N0230
namespace N0646

open Filter Topology
open RealInnerProductSpace
open _root_.GD.N0230.N0685

set_option linter.unusedSectionVars false

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]



def d000537 (u : ℕ → E) (x : E) : Prop :=
  ∀ z : E, Tendsto (fun n ↦ ⟪u n, z⟫) atTop (𝓝 ⟪x, z⟫)

theorem d000538 {u : ℕ → E} {x : E}
    (hu : _root_.GD.N0230.N0646.d000537 u x) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) :
    _root_.GD.N0230.N0646.d000537 (fun n ↦ u (k n)) x := by
  intro z
  exact (hu z).comp hk

theorem d000539 {u : ℕ → E} {x : E}
    (hu : Tendsto u atTop (𝓝 x)) : _root_.GD.N0230.N0646.d000537 u x := by
  intro z
  exact ((continuous_id.inner continuous_const).tendsto x).comp hu

theorem d000537.d000540 {u v : ℕ → E} {x y : E}
    (hu : _root_.GD.N0230.N0646.d000537 u x) (hv : _root_.GD.N0230.N0646.d000537 v y) :
    _root_.GD.N0230.N0646.d000537 (fun n ↦ u n - v n) (x - y) := by
  intro z
  simpa [inner_sub_left] using (hu z).sub (hv z)

theorem d000537.d000541 {u v : ℕ → E} {x y : E}
    (hu : _root_.GD.N0230.N0646.d000537 u x) (hv : _root_.GD.N0230.N0646.d000537 v y) :
    _root_.GD.N0230.N0646.d000537 (fun n ↦ u n + v n) (x + y) := by
  intro z
  simpa [inner_add_left] using (hu z).add (hv z)




def d000542 (u : ℕ → E) (x : E) (n : ℕ) : ℝ :=
  2 * ⟪u n, x⟫ - ‖x‖ ^ 2

theorem d000543 (u : ℕ → E) (x : E) (n : ℕ) :
    _root_.GD.N0230.N0646.d000542 u x n ≤ ‖u n‖ ^ 2 := by
  have hnonneg : 0 ≤ ‖u n - x‖ ^ 2 := sq_nonneg ‖u n - x‖
  rw [norm_sub_sq_real] at hnonneg
  dsimp [_root_.GD.N0230.N0646.d000542]
  linarith

theorem d000537.d000544 {u : ℕ → E} {x : E}
    (hu : _root_.GD.N0230.N0646.d000537 u x) :
    Tendsto (_root_.GD.N0230.N0646.d000542 u x) atTop (𝓝 (‖x‖ ^ 2)) := by
  have hinner : Tendsto (fun n ↦ ⟪u n, x⟫) atTop (𝓝 ⟪x, x⟫) := hu x
  have hconst : Tendsto (fun _ : ℕ ↦ ‖x‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) :=
    tendsto_const_nhds
  have h := (hinner.const_mul 2).sub hconst
  have hlimit : 2 * ⟪x, x⟫ - ‖x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [hlimit] at h
  exact h









theorem d000545
    (C : ℕ → Set E) (Clim : Set E)
    (x p q : ℕ → E) (xlim plim y : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) (x n) (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 Clim xlim plim)
    (hq : ∀ n, q n ∈ C n)
    (hx : Tendsto x atTop (𝓝 xlim))
    (hqlim : Tendsto q atTop (𝓝 plim))
    (hpweak : _root_.GD.N0230.N0646.d000537 p y)
    (hy : y ∈ Clim) :
    Tendsto p atTop (𝓝 plim) := by
  have hxweak : _root_.GD.N0230.N0646.d000537 x xlim := _root_.GD.N0230.N0646.d000539 hx
  have hqweak : _root_.GD.N0230.N0646.d000537 q plim := _root_.GD.N0230.N0646.d000539 hqlim
  have hleftWeak : _root_.GD.N0230.N0646.d000537 (fun n ↦ q n - p n) (plim - y) :=
    hqweak.d000540 hpweak
  have hresWeak : _root_.GD.N0230.N0646.d000537 (fun n ↦ p n - x n) (y - xlim) :=
    hpweak.d000540 hxweak
  let lowerLeft : ℕ → ℝ :=
    _root_.GD.N0230.N0646.d000542 (fun n ↦ q n - p n) (plim - y)
  let lowerRes : ℕ → ℝ :=
    _root_.GD.N0230.N0646.d000542 (fun n ↦ p n - x n) (y - xlim)
  have hlowerLeft : Tendsto lowerLeft atTop (𝓝 (‖plim - y‖ ^ 2)) :=
    hleftWeak.d000544
  have hlowerRes : Tendsto lowerRes atTop (𝓝 (‖y - xlim‖ ^ 2)) :=
    hresWeak.d000544
  have hrhs : Tendsto (fun n ↦ ‖q n - x n‖ ^ 2) atTop (𝓝 (‖plim - xlim‖ ^ 2)) := by
    exact ((hqlim.sub hx).norm.pow 2)
  have hlimitTax :
      ‖plim - y‖ ^ 2 + ‖y - xlim‖ ^ 2 ≤ ‖plim - xlim‖ ^ 2 := by
    apply le_of_tendsto_of_tendsto'
        (hlowerLeft.add hlowerRes) hrhs
    intro n
    have hleft := _root_.GD.N0230.N0646.d000543 (fun k ↦ q k - p k) (plim - y) n
    have hres := _root_.GD.N0230.N0646.d000543 (fun k ↦ p k - x k) (y - xlim) n
    have htax := _root_.GD.N0230.N0685.d000512 (hp n) (hq n)
    dsimp [lowerLeft, lowerRes]
    linarith
  have hreverse :
      ‖y - plim‖ ^ 2 + ‖plim - xlim‖ ^ 2 ≤ ‖y - xlim‖ ^ 2 :=
    _root_.GD.N0230.N0685.d000512 hplim hy
  have hyp : y = plim := by
    have hnormeq : ‖plim - y‖ = ‖y - plim‖ := by
      rw [norm_sub_rev]
    rw [hnormeq] at hlimitTax
    have hzero : ‖y - plim‖ = 0 := by
      nlinarith [norm_nonneg (y - plim)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  subst y
  have hresWeak' : _root_.GD.N0230.N0646.d000537 (fun n ↦ p n - x n) (plim - xlim) :=
    hpweak.d000540 hxweak
  let lowerRes' : ℕ → ℝ :=
    _root_.GD.N0230.N0646.d000542 (fun n ↦ p n - x n) (plim - xlim)
  have hlowerRes' : Tendsto lowerRes' atTop (𝓝 (‖plim - xlim‖ ^ 2)) :=
    hresWeak'.d000544
  have hupper :
      Tendsto (fun n ↦ ‖q n - x n‖ ^ 2 - lowerRes' n) atTop (𝓝 0) := by
    simpa only [sub_self] using hrhs.sub hlowerRes'
  have hsqzero : Tendsto (fun n ↦ ‖q n - p n‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero
      (g := fun n ↦ ‖q n - x n‖ ^ 2 - lowerRes' n) ?_ ?_ hupper
    · intro n
      exact sq_nonneg ‖q n - p n‖
    · intro n
      have hres := _root_.GD.N0230.N0646.d000543
        (fun k ↦ p k - x k) (plim - xlim) n
      have htax := _root_.GD.N0230.N0685.d000512 (hp n) (hq n)
      linarith
  have hnormzero : Tendsto (fun n ↦ ‖q n - p n‖) atTop (𝓝 0) := by
    have hsqrt := hsqzero.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt
  have hdiff : Tendsto (fun n ↦ q n - p n) atTop (𝓝 0) := by
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have := hqlim.sub hdiff
  have hfun : (fun n ↦ q n - (q n - p n)) = p := by
    funext n
    abel
  have hpoint : plim - 0 = plim := sub_zero plim
  rw [hfun, hpoint] at this
  exact this




structure d000546 (C : ℕ → Set E) (Clim : Set E) : Prop where
  weak_liminf :
    ∀ (k : ℕ → ℕ), Tendsto k atTop atTop →
      ∀ (u : ℕ → E) (y : E),
        (∀ n, u n ∈ C (k n)) → _root_.GD.N0230.N0646.d000537 u y → y ∈ Clim
  strong_recovery :
    ∀ y ∈ Clim, ∃ u : ℕ → E,
      (∀ n, u n ∈ C n) ∧ Tendsto u atTop (𝓝 y)



def d000547 (u : ℕ → E) : Prop :=
  ∀ (k : ℕ → ℕ), Tendsto k atTop atTop →
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      ∃ y : E, _root_.GD.N0230.N0646.d000537 (fun n ↦ u (k (m n))) y




def d000548 : Prop :=
  ∀ u : ℕ → E, Bornology.IsBounded (Set.range u) →
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      ∃ y : E, _root_.GD.N0230.N0646.d000537 (fun n ↦ u (k n)) y




theorem d000549 [ProperSpace E] :
    _root_.GD.N0230.N0646.d000548 (E := E) := by
  intro u hu
  obtain ⟨y, _hy, k, hk, hlim⟩ :=
    tendsto_subseq_of_bounded hu (fun n ↦ Set.mem_range_self n)
  refine ⟨k, hk.tendsto_atTop, y, ?_⟩
  exact _root_.GD.N0230.N0646.d000539 (by simpa [Function.comp_def] using hlim)




theorem d000550
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    _root_.GD.N0230.N0646.d000548 (E := E) := by
  intro u hu
  obtain ⟨R, hR⟩ := hu.exists_norm_le
  let f : ℕ → WeakDual ℝ E := fun n ↦
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u n))
  have hfmem : ∀ n,
      f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) R := by
    intro n
    change dist (WeakDual.toStrongDual (f n)) 0 ≤ R
    simpa [f, dist_eq_norm, WeakDual.toStrongDual,
      StrongDual.toWeakDual] using hR (u n) (Set.mem_range_self n)
  obtain ⟨φ, _hφmem, k, hk, hklim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) R) hfmem
  let y : E :=
    (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual φ)
  refine ⟨k, hk.tendsto_atTop, y, ?_⟩
  intro z
  have heval : Tendsto (fun n ↦ (f (k n)) z) atTop (𝓝 (φ z)) :=
    ((WeakDual.eval_continuous z).tendsto φ).comp hklim
  simpa [f, y, Function.comp_def,
    InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_symm_apply] using heval



theorem d000551
    (C : ℕ → Set E) (x p q : ℕ → E) (xlim qlim : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) (x n) (p n))
    (hq : ∀ n, q n ∈ C n)
    (hx : Tendsto x atTop (𝓝 xlim))
    (hqlim : Tendsto q atTop (𝓝 qlim)) :
    Bornology.IsBounded (Set.range p) := by
  obtain ⟨Mx, hMx⟩ :=
    (Metric.isBounded_range_of_tendsto x hx).exists_norm_le
  obtain ⟨Mq, hMq⟩ :=
    (Metric.isBounded_range_of_tendsto q hqlim).exists_norm_le
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Mq + 2 * Mx, ?_⟩
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  have hxn : ‖x n‖ ≤ Mx := hMx (x n) ⟨n, rfl⟩
  have hqn : ‖q n‖ ≤ Mq := hMq (q n) ⟨n, rfl⟩
  have htax := _root_.GD.N0230.N0685.d000512 (hp n) (hq n)
  have hpx : ‖p n - x n‖ ≤ ‖q n - x n‖ := by
    nlinarith [sq_nonneg ‖q n - p n‖,
      norm_nonneg (p n - x n), norm_nonneg (q n - x n)]
  calc
    ‖p n‖ ≤ ‖p n - x n‖ + ‖x n‖ := by
      simpa only [sub_add_cancel] using norm_add_le (p n - x n) (x n)
    _ ≤ ‖q n - x n‖ + ‖x n‖ := add_le_add hpx le_rfl
    _ ≤ (‖q n‖ + ‖x n‖) + ‖x n‖ := by
      gcongr
      exact norm_sub_le (q n) (x n)
    _ ≤ Mq + 2 * Mx := by linarith

theorem d000552
    (hcompact : _root_.GD.N0230.N0646.d000548 (E := E))
    {u : ℕ → E} (hu : Bornology.IsBounded (Set.range u)) :
    _root_.GD.N0230.N0646.d000547 u := by
  intro k hk
  have hrange : Set.range (fun n ↦ u (k n)) ⊆ Set.range u := by
    rintro _ ⟨n, rfl⟩
    exact ⟨k n, rfl⟩
  obtain ⟨m, hm, y, hy⟩ := hcompact (fun n ↦ u (k n)) (hu.subset hrange)
  exact ⟨m, hm, y, hy⟩






theorem d000553
    (C : ℕ → Set E) (Clim : Set E)
    (x p : ℕ → E) (xlim plim : E)
    (hmosco : _root_.GD.N0230.N0646.d000546 C Clim)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) (x n) (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 Clim xlim plim)
    (hx : Tendsto x atTop (𝓝 xlim))
    (hcompact : _root_.GD.N0230.N0646.d000547 p) :
    Tendsto p atTop (𝓝 plim) := by
  apply tendsto_of_subseq_tendsto
  intro k hk
  obtain ⟨m, hm, y, hpweak⟩ := hcompact k hk
  let km : ℕ → ℕ := fun n ↦ k (m n)
  have hkm : Tendsto km atTop atTop := hk.comp hm
  have hy : y ∈ Clim := by
    apply hmosco.weak_liminf km hkm (fun n ↦ p (km n)) y
    · intro n
      exact (hp (km n)).1
    · exact hpweak
  obtain ⟨q, hq, hqlim⟩ := hmosco.strong_recovery plim hplim.1
  refine ⟨m, ?_⟩
  exact _root_.GD.N0230.N0646.d000545
    (fun n ↦ C (km n)) Clim
    (fun n ↦ x (km n)) (fun n ↦ p (km n)) (fun n ↦ q (km n))
    xlim plim y
    (fun n ↦ hp (km n)) hplim (fun n ↦ hq (km n))
    (hx.comp hkm) (hqlim.comp hkm) hpweak hy




theorem d000554
    (C : ℕ → Set E) (Clim : Set E)
    (x p : ℕ → E) (xlim plim : E)
    (hmosco : _root_.GD.N0230.N0646.d000546 C Clim)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) (x n) (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 Clim xlim plim)
    (hx : Tendsto x atTop (𝓝 xlim))
    (hweakCompact : _root_.GD.N0230.N0646.d000548 (E := E)) :
    Tendsto p atTop (𝓝 plim) := by
  obtain ⟨q, hq, hqlim⟩ := hmosco.strong_recovery plim hplim.1
  have hpBounded : Bornology.IsBounded (Set.range p) :=
    _root_.GD.N0230.N0646.d000551 C x p q xlim plim hp hq hx hqlim
  exact _root_.GD.N0230.N0646.d000553 C Clim x p xlim plim
    hmosco hp hplim hx
    (_root_.GD.N0230.N0646.d000552 hweakCompact hpBounded)



theorem d000555
    [ProperSpace E]
    (C : ℕ → Set E) (Clim : Set E)
    (x p : ℕ → E) (xlim plim : E)
    (hmosco : _root_.GD.N0230.N0646.d000546 C Clim)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) (x n) (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 Clim xlim plim)
    (hx : Tendsto x atTop (𝓝 xlim)) :
    Tendsto p atTop (𝓝 plim) :=
  _root_.GD.N0230.N0646.d000554
    C Clim x p xlim plim hmosco hp hplim hx
    _root_.GD.N0230.N0646.d000549



theorem d000556
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (C : ℕ → Set E) (Clim : Set E)
    (x p : ℕ → E) (xlim plim : E)
    (hmosco : _root_.GD.N0230.N0646.d000546 C Clim)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) (x n) (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 Clim xlim plim)
    (hx : Tendsto x atTop (𝓝 xlim)) :
    Tendsto p atTop (𝓝 plim) :=
  _root_.GD.N0230.N0646.d000554
    C Clim x p xlim plim hmosco hp hplim hx
    _root_.GD.N0230.N0646.d000550

section ChosenProjection

variable [CompleteSpace E]


noncomputable def d000557
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) : E :=
  Classical.choose
    (_root_.GD.N0230.N0685.d000521 hne hclosed.isComplete hconv x)

theorem d000558
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) :
    _root_.GD.N0230.N0685.d000511 C x (_root_.GD.N0230.N0646.d000557 C hne hclosed hconv x) :=
  Classical.choose_spec
    (_root_.GD.N0230.N0685.d000521 hne hclosed.isComplete hconv x)





theorem d000559
    (C : ℕ → Set E) (Clim : Set E)
    (hne : ∀ n, (C n).Nonempty) (hneLim : Clim.Nonempty)
    (hclosed : ∀ n, IsClosed (C n)) (hclosedLim : IsClosed Clim)
    (hconv : ∀ n, Convex ℝ (C n)) (hconvLim : Convex ℝ Clim)
    (x : ℕ → E) (xlim : E)
    (hmosco : _root_.GD.N0230.N0646.d000546 C Clim)
    (hx : Tendsto x atTop (𝓝 xlim))
    (hweakCompact : _root_.GD.N0230.N0646.d000548 (E := E)) :
    Tendsto
      (fun n ↦ _root_.GD.N0230.N0646.d000557 (C n) (hne n) (hclosed n) (hconv n) (x n))
      atTop
      (𝓝 (_root_.GD.N0230.N0646.d000557 Clim hneLim hclosedLim hconvLim xlim)) := by
  apply _root_.GD.N0230.N0646.d000554
    C Clim x
    (fun n ↦ _root_.GD.N0230.N0646.d000557 (C n) (hne n) (hclosed n) (hconv n) (x n))
    xlim (_root_.GD.N0230.N0646.d000557 Clim hneLim hclosedLim hconvLim xlim)
    hmosco
  · intro n
    exact _root_.GD.N0230.N0646.d000558 (C n) (hne n) (hclosed n) (hconv n) (x n)
  · exact _root_.GD.N0230.N0646.d000558 Clim hneLim hclosedLim hconvLim xlim
  · exact hx
  · exact hweakCompact


theorem d000560
    [ProperSpace E]
    (C : ℕ → Set E) (Clim : Set E)
    (hne : ∀ n, (C n).Nonempty) (hneLim : Clim.Nonempty)
    (hclosed : ∀ n, IsClosed (C n)) (hclosedLim : IsClosed Clim)
    (hconv : ∀ n, Convex ℝ (C n)) (hconvLim : Convex ℝ Clim)
    (x : ℕ → E) (xlim : E)
    (hmosco : _root_.GD.N0230.N0646.d000546 C Clim)
    (hx : Tendsto x atTop (𝓝 xlim)) :
    Tendsto
      (fun n ↦ _root_.GD.N0230.N0646.d000557 (C n) (hne n) (hclosed n) (hconv n) (x n))
      atTop
      (𝓝 (_root_.GD.N0230.N0646.d000557 Clim hneLim hclosedLim hconvLim xlim)) :=
  _root_.GD.N0230.N0646.d000559 C Clim hne hneLim hclosed hclosedLim
    hconv hconvLim x xlim hmosco hx
    _root_.GD.N0230.N0646.d000549


theorem d000561
    [TopologicalSpace.SeparableSpace E]
    (C : ℕ → Set E) (Clim : Set E)
    (hne : ∀ n, (C n).Nonempty) (hneLim : Clim.Nonempty)
    (hclosed : ∀ n, IsClosed (C n)) (hclosedLim : IsClosed Clim)
    (hconv : ∀ n, Convex ℝ (C n)) (hconvLim : Convex ℝ Clim)
    (x : ℕ → E) (xlim : E)
    (hmosco : _root_.GD.N0230.N0646.d000546 C Clim)
    (hx : Tendsto x atTop (𝓝 xlim)) :
    Tendsto
      (fun n ↦ _root_.GD.N0230.N0646.d000557 (C n) (hne n) (hclosed n) (hconv n) (x n))
      atTop
      (𝓝 (_root_.GD.N0230.N0646.d000557 Clim hneLim hclosedLim hconvLim xlim)) :=
  _root_.GD.N0230.N0646.d000559 C Clim hne hneLim hclosed hclosedLim
    hconv hconvLim x xlim hmosco hx
    _root_.GD.N0230.N0646.d000550

end ChosenProjection

end N0646
end N0230
end GD
