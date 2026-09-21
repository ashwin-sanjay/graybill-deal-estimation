import GD.Module0200















open Filter Set Topology
open scoped ContDiff

namespace GD.N0232.N0720.N1318

open _root_.GD.N0232.N0720.N1352

noncomputable section




theorem d002808 (D : ℕ)
    {H M₀ M₁ : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739} {a : ℝ}
    (hne : M₀ x ≠ 0)
    (hp : M₁ x = H x * M₀ x)
    (hpa : M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) = H (_root_.GD.N0232.N0720.N1352.d002795 x a) * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a))
    (h0 : a ^ D * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₀ x)
    (h1 : a ^ (D + 1) * M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₁ x) :
    a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) = H x := by
  apply mul_right_cancel₀ hne
  calc
    a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) * M₀ x =
        a ^ (D + 1) * (H (_root_.GD.N0232.N0720.N1352.d002795 x a) * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a)) := by
      rw [← h0, pow_succ]
      ring
    _ = a ^ (D + 1) * M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) := by rw [hpa]
    _ = M₁ x := h1
    _ = H x * M₀ x := hp

private theorem d002809 (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1352.d002753 G x = _root_.GD.N0232.N0720.N1352.d002740 0 + (_root_.GD.N0232.N0720.N1352.d002804 G x - x 0) • _root_.GD.N0232.N0720.N1352.d002740 2 := by
  simp [_root_.GD.N0232.N0720.N1352.d002753, _root_.GD.N0232.N0720.N1352.d002804]

private theorem d002810 (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1352.d002754 G x = _root_.GD.N0232.N0720.N1352.d002740 1 + (_root_.GD.N0232.N0720.N1352.d002804 G x - x 1) • _root_.GD.N0232.N0720.N1352.d002740 3 := by
  have h : _root_.GD.N0232.N0720.N1352.d002742 x * (G x - 1) = _root_.GD.N0232.N0720.N1352.d002804 G x - x 1 := by
    unfold _root_.GD.N0232.N0720.N1352.d002804 _root_.GD.N0232.N0720.N1352.d002742
    ring
  rw [_root_.GD.N0232.N0720.N1352.d002754, h]





theorem d002811 (D : ℕ)
    {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s) (c : _root_.GD.N0232.N0720.N1352.d002752 s)
    {H M₀ M₁ N₀ N₁ : _root_.GD.N0232.N0720.N1352.d002739 → ℝ}
    (hH : ContDiffOn ℝ 2 H s)
    (hM₀ : ContDiffOn ℝ ∞ M₀ s) (hM₁ : ContDiffOn ℝ ∞ M₁ s)
    (hM₀ne : ∀ y ∈ s, M₀ y ≠ 0)
    (hratio : ∀ y ∈ s, M₁ y = H y * M₀ y)
    (hN₀ : ∀ y ∈ s, N₀ y = _root_.GD.N0232.N0720.N1352.d002804 c.G y * M₀ y)
    (hN₁ : ∀ y ∈ s, N₁ y = _root_.GD.N0232.N0720.N1352.d002804 c.G y * M₁ y)
    (hpde₀ : ∀ y ∈ s,
      fderiv ℝ N₀ y (_root_.GD.N0232.N0720.N1352.d002740 2) = y 0 * fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 2) -
        fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
      fderiv ℝ N₀ y (_root_.GD.N0232.N0720.N1352.d002740 3) = y 1 * fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 3) -
        fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 1))
    (hpde₁ : ∀ y ∈ s,
      fderiv ℝ N₁ y (_root_.GD.N0232.N0720.N1352.d002740 2) = y 0 * fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 2) -
        fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
      fderiv ℝ N₁ y (_root_.GD.N0232.N0720.N1352.d002740 3) = y 1 * fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 3) -
        fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 1))
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ s) (hd : _root_.GD.N0232.N0720.N1352.d002742 x = 0)
    (hF : _root_.GD.N0232.N0720.N1352.d002762 c.G c.Gz c.Gw c.Gu x ≠ 0) (hM₁x : M₁ x ≠ 0)
    (hdegrees : ∀ᶠ a : ℝ in 𝓝 1,
      a ^ D * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₀ x ∧
      a ^ (D + 1) * M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₁ x) : False := by
  have hδ : ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002804 c.G) s := by
    have hcoordinate : ContDiffOn ℝ ∞ (fun y : _root_.GD.N0232.N0720.N1352.d002739 ↦ y 0) s := by fun_prop
    exact hcoordinate.add (_root_.GD.N0232.N0720.N1352.d002748.contDiffOn.mul c.smooth_G)
  have htransport (y : _root_.GD.N0232.N0720.N1352.d002739) (hy : y ∈ s) :
      fderiv ℝ H y (_root_.GD.N0232.N0720.N1352.d002753 c.G y) = 0 ∧
      fderiv ℝ H y (_root_.GD.N0232.N0720.N1352.d002754 c.G y) = 0 := by
    have hHy := (hH.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
    have h0y := (hM₀.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
    have h1y := (hM₁.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
    have hδy := (hδ.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
    have he₀ : N₀ =ᶠ[𝓝 y] fun z ↦ _root_.GD.N0232.N0720.N1352.d002804 c.G z * M₀ z := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hN₀ z hz
    have he₁ : N₁ =ᶠ[𝓝 y] fun z ↦ _root_.GD.N0232.N0720.N1352.d002804 c.G z * M₁ z := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hN₁ z hz
    have her : M₁ =ᶠ[𝓝 y] fun z ↦ H z * M₀ z := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hratio z hz
    constructor
    · apply _root_.GD.N0232.N0720.N1352.d002801 hHy h0y her (hM₀ne y hy)
        (a := -fderiv ℝ (_root_.GD.N0232.N0720.N1352.d002804 c.G) y (_root_.GD.N0232.N0720.N1352.d002740 2))
      · rw [_root_.GD.N0232.N0720.N1318.d002809]
        exact _root_.GD.N0232.N0720.N1352.d002802 0 2 hδy h0y he₀ (hpde₀ y hy).1
      · rw [_root_.GD.N0232.N0720.N1318.d002809]
        exact _root_.GD.N0232.N0720.N1352.d002802 0 2 hδy h1y he₁ (hpde₁ y hy).1
    · apply _root_.GD.N0232.N0720.N1352.d002801 hHy h0y her (hM₀ne y hy)
        (a := -fderiv ℝ (_root_.GD.N0232.N0720.N1352.d002804 c.G) y (_root_.GD.N0232.N0720.N1352.d002740 3))
      · rw [_root_.GD.N0232.N0720.N1318.d002810]
        exact _root_.GD.N0232.N0720.N1352.d002802 1 3 hδy h0y he₀ (hpde₀ y hy).2
      · rw [_root_.GD.N0232.N0720.N1318.d002810]
        exact _root_.GD.N0232.N0720.N1352.d002802 1 3 hδy h1y he₁ (hpde₁ y hy).2
  have hHx : H x ≠ 0 := by
    intro hz
    apply hM₁x
    simp [hratio x hx, hz]
  have hstay : ∀ᶠ a : ℝ in 𝓝 1, _root_.GD.N0232.N0720.N1352.d002795 x a ∈ s :=
    (_root_.GD.N0232.N0720.N1352.d002798 x).continuousAt.eventually
      (by simpa using hs.mem_nhds hx)
  have hhom : ∀ᶠ a : ℝ in 𝓝 1, a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) = H x := by
    filter_upwards [hdegrees, hstay] with a ha has
    exact _root_.GD.N0232.N0720.N1318.d002808 D (hM₀ne x hx)
      (hratio x hx) (hratio _ has) ha.1 ha.2
  exact _root_.GD.N0232.N0720.N1352.d002800 hs c hH
    (fun y hy ↦ (htransport y hy).1) (fun y hy ↦ (htransport y hy).2)
    hx hd hF hHx hhom

end
end GD.N0232.N0720.N1318

#print axioms _root_.GD.N0232.N0720.N1318.d002808
#print axioms _root_.GD.N0232.N0720.N1318.d002811
