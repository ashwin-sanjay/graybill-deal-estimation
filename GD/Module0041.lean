import Mathlib
































namespace GD
namespace N0230
namespace N0685

open RealInnerProductSpace

set_option linter.unusedSectionVars false

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]




def d000511 (K : Set E) (x p : E) : Prop :=
  p ∈ K ∧ ∀ e ∈ K, ⟪x - p, e - p⟫ ≤ 0



theorem d000512 {K : Set E} {x p : E} (hp : _root_.GD.N0230.N0685.d000511 K x p)
    {e : E} (he : e ∈ K) :
    ‖e - p‖ ^ 2 + ‖p - x‖ ^ 2 ≤ ‖e - x‖ ^ 2 := by
  have hip : ⟪x - p, e - p⟫ ≤ 0 := hp.2 e he
  have hdecomp : e - x = (e - p) + (p - x) := by abel
  have hexp : ‖e - x‖ ^ 2 =
      ‖e - p‖ ^ 2 + 2 * ⟪e - p, p - x⟫ + ‖p - x‖ ^ 2 := by
    rw [hdecomp, ← real_inner_self_eq_norm_sq, real_inner_add_add_self,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hpos : 0 ≤ ⟪e - p, p - x⟫ := by
    have : ⟪e - p, p - x⟫ = -⟪x - p, e - p⟫ := by
      rw [real_inner_comm]
      have : (p : E) - x = -(x - p) := by abel
      rw [this, inner_neg_left]
    linarith [hip, this]
  nlinarith [hexp, hpos]





theorem d000513 {K : Set E} {x y p q : E}
    (hp : _root_.GD.N0230.N0685.d000511 K x p) (hq : _root_.GD.N0230.N0685.d000511 K y q) :
    ‖q - p‖ ^ 2 ≤ ‖q - x‖ ^ 2 - ‖p - x‖ ^ 2 := by
  have := _root_.GD.N0230.N0685.d000512 hp hq.1
  linarith


theorem d000514 {K : Set E} {x p q : E}
    (hp : _root_.GD.N0230.N0685.d000511 K x p) (hq : _root_.GD.N0230.N0685.d000511 K x q) : p = q := by
  have h1 : ⟪x - p, q - p⟫ ≤ 0 := hp.2 q hq.1
  have h2 : ⟪x - q, p - q⟫ ≤ 0 := hq.2 p hp.1
  have hsum : ⟪x - p, q - p⟫ + ⟪x - q, p - q⟫ = ‖q - p‖ ^ 2 := by
    have e1 : (p : E) - q = -(q - p) := by abel
    rw [e1, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
    have e2 : x - p - (x - q) = q - p := by abel
    rw [e2, real_inner_self_eq_norm_sq]
  have h0 : ‖q - p‖ = 0 := by nlinarith [norm_nonneg (q - p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm




theorem d000515 (T : E ≃ₗᵢ[ℝ] F) {K : Set E} {x p : E}
    (hp : _root_.GD.N0230.N0685.d000511 K x p) :
    _root_.GD.N0230.N0685.d000511 (T '' K) (T x) (T p) := by
  refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
  rintro e ⟨w, hw, rfl⟩
  have : ⟪T x - T p, T w - T p⟫ = ⟪x - p, w - p⟫ := by
    rw [← LinearIsometryEquiv.map_sub, ← LinearIsometryEquiv.map_sub]
    exact T.inner_map_map _ _
  rw [this]
  exact hp.2 w hw





theorem d000516 {K : Set E} {x y p q : E}
    (hp : _root_.GD.N0230.N0685.d000511 K x p) (hq : _root_.GD.N0230.N0685.d000511 K y q) :
    ‖q - p‖ ≤ ‖y - x‖ := by
  have h1 : ⟪x - p, q - p⟫ ≤ 0 := hp.2 q hq.1
  have h2 : ⟪y - q, p - q⟫ ≤ 0 := hq.2 p hp.1
  have h2' : 0 ≤ ⟪y - q, q - p⟫ := by
    have e1 : (p : E) - q = -(q - p) := by abel
    rw [e1, inner_neg_right] at h2
    linarith
  have hdec : (q : E) - p = (q - y) + ((y - x) + (x - p)) := by abel
  have hexp : ⟪q - p, q - p⟫ =
      ⟪q - p, q - y⟫ + ⟪q - p, y - x⟫ + ⟪q - p, x - p⟫ := by
    calc ⟪q - p, q - p⟫ = ⟪q - p, (q - y) + ((y - x) + (x - p))⟫ := by
          rw [← hdec]
    _ = ⟪q - p, q - y⟫ + (⟪q - p, y - x⟫ + ⟪q - p, x - p⟫) := by
          rw [inner_add_right, inner_add_right]
    _ = _ := by ring
  have hterm1 : ⟪q - p, q - y⟫ ≤ 0 := by
    have e2 : (q : E) - y = -(y - q) := by abel
    rw [e2, inner_neg_right, real_inner_comm]
    linarith
  have hterm3 : ⟪q - p, x - p⟫ ≤ 0 := by
    rw [real_inner_comm]; exact h1
  have hcs : ⟪q - p, y - x⟫ ≤ ‖q - p‖ * ‖y - x‖ := real_inner_le_norm _ _
  have hineq : ‖q - p‖ ^ 2 ≤ ‖q - p‖ * ‖y - x‖ := by
    rw [← real_inner_self_eq_norm_sq, hexp]
    linarith
  rcases eq_or_lt_of_le (norm_nonneg (q - p)) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith






theorem d000517 {T : E → E} (hiso : ∀ a b, ‖T a - T b‖ = ‖a - b‖)
    {K : Set E} {x p : E}
    (hK : ∀ a ∈ K, T a ∈ K) (hx : T x = x) (hp : _root_.GD.N0230.N0685.d000511 K x p) :
    T p = p := by
  have hTp : T p ∈ K := hK p hp.1
  have htax := _root_.GD.N0230.N0685.d000512 hp hTp
  have hdist : ‖T p - x‖ = ‖p - x‖ := by
    calc ‖T p - x‖ = ‖T p - T x‖ := by rw [hx]
    _ = ‖p - x‖ := hiso p x
  rw [hdist] at htax
  have h0 : ‖T p - p‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖T p - p‖ = 0 := by nlinarith [norm_nonneg (T p - p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)




theorem d000518 (T : E ≃ₗᵢ[ℝ] E) {K : Set E} {x p : E}
    (hK : T '' K = K) (hp : _root_.GD.N0230.N0685.d000511 K x p) :
    ‖T p - p‖ ^ 2 ≤ ‖T p - x‖ ^ 2 - ‖p - x‖ ^ 2 := by
  have hq : _root_.GD.N0230.N0685.d000511 K (T x) (T p) := by
    have := _root_.GD.N0230.N0685.d000515 T hp
    rwa [hK] at this
  exact _root_.GD.N0230.N0685.d000513 hp hq





theorem d000519 (T : E ≃ₗᵢ[ℝ] E) {K : Set E} {x p : E}
    (hK : T '' K = K) (hp : _root_.GD.N0230.N0685.d000511 K x p) :
    ‖T p - p‖ ^ 2 ≤ ‖T x - x‖ * (‖T x - x‖ + 2 * ‖p - x‖) := by
  have h1 := _root_.GD.N0230.N0685.d000518 T hK hp
  have h2 : ‖T p - x‖ ≤ ‖p - x‖ + ‖T x - x‖ := by
    have : T p - x = (T p - T x) + (T x - x) := by abel
    calc ‖T p - x‖ = ‖(T p - T x) + (T x - x)‖ := by rw [← this]
    _ ≤ ‖T p - T x‖ + ‖T x - x‖ := norm_add_le _ _
    _ = ‖p - x‖ + ‖T x - x‖ := by
        rw [← LinearIsometryEquiv.map_sub, T.norm_map]
  nlinarith [h1, h2, norm_nonneg (T p - x), norm_nonneg (p - x),
    norm_nonneg (T x - x)]






theorem d000520 (T : E ≃ₗᵢ[ℝ] E) {K : Set E} {x p : E}
    (hK : T '' K = K) (hp : _root_.GD.N0230.N0685.d000511 K x p) :
    ‖T p - p‖ ≤ ‖T x - x‖ := by
  have hq : _root_.GD.N0230.N0685.d000511 K (T x) (T p) := by
    have := _root_.GD.N0230.N0685.d000515 T hp
    rwa [hK] at this
  exact _root_.GD.N0230.N0685.d000516 hp hq





theorem d000521 {K : Set E} (hne : K.Nonempty) (hcomp : IsComplete K)
    (hconv : Convex ℝ K) (x : E) : ∃ p, _root_.GD.N0230.N0685.d000511 K x p := by
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcomp hconv x
  exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin⟩




theorem d000522 [CompleteSpace E]
    (p : ℕ → E) (d : ℕ → ℝ) (hd : ∀ n, dist (p n) (p (n + 1)) ≤ d n)
    (hsum : Summable d) :
    ∃ q : E, Filter.Tendsto p Filter.atTop (nhds q) := by
  have hc : CauchySeq p := cauchySeq_of_dist_le_of_summable d hd hsum
  exact cauchySeq_tendsto_of_complete hc




theorem d000523 {T : E → E} (hT : Continuous T)
    (p : ℕ → E) (q : E)
    (hshift : ∀ n, T (p n) = p (n + 1))
    (hlim : Filter.Tendsto p Filter.atTop (nhds q)) :
    T q = q := by
  have h1 : Filter.Tendsto (fun n => T (p n)) Filter.atTop (nhds (T q)) :=
    (hT.tendsto q).comp hlim
  have h2 : Filter.Tendsto (fun n => p (n + 1)) Filter.atTop (nhds q) :=
    hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have h3 : Filter.Tendsto (fun n => T (p n)) Filter.atTop (nhds q) := by
    simpa only [hshift] using h2
  exact tendsto_nhds_unique h1 h3








theorem d000524 {α : Type*} {K : Set α} {ρ : α → ℝ} {T : α → α}
    (hK : ∀ a ∈ K, T a ∈ K) (hρ : ∀ a ∈ K, ρ (T a) = ρ a)
    {p : α} (hpK : p ∈ K) (hmin : ∀ a ∈ K, p ≠ a → ρ p < ρ a) :
    T p = p := by
  by_contra hne
  have hTp : T p ∈ K := hK p hpK
  have hlt : ρ p < ρ (T p) := hmin (T p) hTp (fun h => hne h.symm)
  rw [hρ p hpK] at hlt
  exact lt_irrefl _ hlt








theorem d000525 {α : Type*} {K : Set α} {ρ : α → ℝ}
    {T : α → α} {cw : ℝ} (hc : 0 < cw)
    (hK : ∀ a ∈ K, T a ∈ K)
    (hsurj : ∀ b ∈ K, ∃ a ∈ K, T a = b)
    (hρ : ∀ a ∈ K, ρ (T a) = cw * ρ a)
    {p : α} (hpK : p ∈ K) (hmin : ∀ a ∈ K, p ≠ a → ρ p < ρ a) :
    T p = p := by
  by_contra hne
  have hTp : T p ∈ K := hK p hpK
  have hlt : ρ p < ρ (T p) := hmin (T p) hTp (fun h => hne h.symm)
  have hminTp : ∀ b ∈ K, ρ (T p) ≤ ρ b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hsurj b hb
    rw [hρ a ha, hρ p hpK]
    rcases eq_or_ne p a with h | h
    · rw [h]
    · nlinarith [hmin a ha h]
  linarith [hminTp p hpK]












theorem d000526
    {α : Type*} {K : Set α} {ρ : α → ℝ} {T : α → α}
    {cw offset : ℝ} (hc : 0 < cw)
    (hK : ∀ a ∈ K, T a ∈ K)
    (hsurj : ∀ b ∈ K, ∃ a ∈ K, T a = b)
    (hρ : ∀ a ∈ K, ρ (T a) = cw * ρ a + offset)
    {p : α} (hpK : p ∈ K) (hmin : ∀ a ∈ K, p ≠ a → ρ p < ρ a) :
    T p = p := by
  by_contra hne
  have hTp : T p ∈ K := hK p hpK
  have hlt : ρ p < ρ (T p) :=
    hmin (T p) hTp (fun h ↦ hne h.symm)
  have hminTp : ∀ b ∈ K, ρ (T p) ≤ ρ b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hsurj b hb
    rw [hρ a ha, hρ p hpK]
    rcases eq_or_ne p a with h | h
    · rw [h]
    · nlinarith [hmin a ha h]
  linarith [hminTp p hpK]

end N0685
end N0230
end GD

#print axioms _root_.GD.N0230.N0685.d000526
