import GD.Module1216
import GD.Module0004
















open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1326

noncomputable section

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1342
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0556
open _root_.GD.N0238.N0753

abbrev d019882 := _root_.GD.N0232.N0720.N1080.d014168

variable {k : ℕ}

theorem d019883 (h : _root_.GD.N0232.N0720.N1341.d004415 k → ℝ)
    (x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k))) :
    _root_.GD.N0232.N0720.N1341.d004418 h x.1 = ‖x.1‖ * h ((homeomorphUnitSphereProd _ x).1) := by
  have hx : x.1 ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  unfold _root_.GD.N0232.N0720.N1341.d004418 _root_.GD.N0238.N0753.d004402
  rw [dif_neg hx]
  change ‖x.1‖ * h _ = ‖x.1‖ * h _
  congr 1
  apply congrArg h
  apply Subtype.ext
  simp only [_root_.GD.N0238.N0753.d004399, homeomorphUnitSphereProd_apply_fst_coe]

theorem d019884 {h : _root_.GD.N0232.N0720.N1341.d004415 k → ℝ} (hh : Measurable h) :
    Measurable (_root_.GD.N0232.N0720.N1341.d004418 h) := by
  apply measurable_of_measurable_on_compl_singleton 0
  change Measurable (fun x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) ↦ _root_.GD.N0232.N0720.N1341.d004418 h x.1)
  simp_rw [_root_.GD.N0232.N0720.N1326.d019883]
  exact measurable_subtype_coe.norm.mul
    (hh.comp (homeomorphUnitSphereProd _).measurable.fst)

@[fun_prop]
theorem d019885 (h : _root_.GD.N0232.N0720.N1341.d004417 k) : Measurable (_root_.GD.N0232.N0720.N1341.d004418 h) :=
  _root_.GD.N0232.N0720.N1326.d019884 (Lp.stronglyMeasurable h).measurable



theorem d019886 {h j : _root_.GD.N0232.N0720.N1341.d004415 k → ℝ}
    (hhj : h =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 k] j) :
    _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[volume] _root_.GD.N0232.N0720.N1341.d004418 j := by
  have hprod :
      (fun p : _root_.GD.N0232.N0720.N1341.d004415 k × Ioi (0 : ℝ) ↦
        _root_.GD.N0232.N0720.N1341.d004418 h (((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)).symm p).1)) =ᵐ[
          (_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)]
      (fun p : _root_.GD.N0232.N0720.N1341.d004415 k × Ioi (0 : ℝ) ↦
        _root_.GD.N0232.N0720.N1341.d004418 j (((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)).symm p).1)) := by
    have hfst : (fun p : _root_.GD.N0232.N0720.N1341.d004415 k × Ioi (0 : ℝ) ↦ h p.1) =ᵐ[
        (_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)] (fun p ↦ j p.1) :=
      (Measure.quasiMeasurePreserving_fst
        (μ := _root_.GD.N0232.N0720.N1341.d004416 k) (ν := Measure.volumeIoiPow k)).ae_eq_comp hhj
    filter_upwards [hfst] with p hp
    simp only [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0720.N1341.d004421]
    exact congrArg (fun v : ℝ ↦ p.2.1 * v) hp
  have hpolar :=
    (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)).measurePreserving_homeomorphUnitSphereProd
  have hsub : (fun x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) ↦ _root_.GD.N0232.N0720.N1341.d004418 h x.1) =ᵐ[
      volume.comap Subtype.val] (fun x ↦ _root_.GD.N0232.N0720.N1341.d004418 j x.1) := by
    have hh := hpolar.quasiMeasurePreserving.ae_eq_comp (by
      simpa only [finrank_euclideanSpace_fin, Nat.add_sub_cancel, _root_.GD.N0232.N0720.N1341.d004416] using hprod)
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hh
  have hr : _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[
      (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)).restrict ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k))]
      _root_.GD.N0232.N0720.N1341.d004418 j :=
    (ae_restrict_iff_subtype (μ := (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)))
      (p := fun x : _root_.GD.N0232.N0720.N1341.d004414 k ↦ _root_.GD.N0232.N0720.N1341.d004418 h x = _root_.GD.N0232.N0720.N1341.d004418 j x)
      (measurableSet_singleton (0 : _root_.GD.N0232.N0720.N1341.d004414 k)).compl).2 hsub
  simpa only [restrict_compl_singleton] using hr

theorem d019887 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ)
    (hf : _root_.GD.N0238.N0753.d004397 f) :
    _root_.GD.N0232.N0720.N1341.d004418 (fun u : _root_.GD.N0232.N0720.N1341.d004415 k ↦ f u) = f := by
  apply _root_.GD.N0238.N0753.d004410 _ _ (_root_.GD.N0232.N0720.N1341.d004419 _) hf
  intro u
  exact _root_.GD.N0232.N0720.N1341.d004420 _ ⟨u.1, mem_sphere_zero_iff_norm.mpr u.2⟩

theorem d019888 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ C) :
    MemLp (fun u : _root_.GD.N0232.N0720.N1341.d004415 k ↦ f u) 2 (_root_.GD.N0232.N0720.N1341.d004416 k) :=
  MemLp.of_bound (hf.comp measurable_subtype_coe).aestronglyMeasurable C
    (ae_of_all _ hbound)

def d019889 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ C) : _root_.GD.N0232.N0720.N1341.d004417 k :=
  (_root_.GD.N0232.N0720.N1326.d019888 f hf C hbound).toLp (fun u : _root_.GD.N0232.N0720.N1341.d004415 k ↦ f u)

theorem d019890 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ C) :
    _root_.GD.N0232.N0720.N1326.d019889 f hf C hbound =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 k] (fun u : _root_.GD.N0232.N0720.N1341.d004415 k ↦ f u) :=
  (_root_.GD.N0232.N0720.N1326.d019888 f hf C hbound).coeFn_toLp

theorem d019891 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f)
    (hhom : _root_.GD.N0238.N0753.d004397 f) (C : ℝ)
    (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ C) :
    _root_.GD.N0232.N0720.N1341.d004418 (_root_.GD.N0232.N0720.N1326.d019889 f hf C hbound) =ᵐ[volume] f := by
  have h := _root_.GD.N0232.N0720.N1326.d019886 (_root_.GD.N0232.N0720.N1326.d019890 f hf C hbound)
  rwa [_root_.GD.N0232.N0720.N1326.d019887 f hhom] at h

variable (m n k : ℕ) (hdim : m + n = k + 1)


def d019892 (q : _root_.GD.N0232.N0720.N1329.d019646) (h : _root_.GD.N0232.N0720.N1341.d004417 k) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004469 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim q) h

def d019893 (h : _root_.GD.N0232.N0720.N1341.d004417 k) (omega : _root_.GD.N0232.N0720.N1329.d019645 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1341.d004418 h (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim omega)

@[fun_prop]
theorem d019894 (h : _root_.GD.N0232.N0720.N1341.d004417 k) : Measurable (_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h) :=
  (_root_.GD.N0232.N0720.N1326.d019885 h).comp (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).measurable

private theorem d019895 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    0 ≤ _root_.GD.N0232.N0720.N1316.d004445 q x :=
  mul_nonneg (_root_.GD.N0232.N0720.N1316.d004446 q).le (Real.exp_pos _).le

@[fun_prop]
private theorem d019896 (q : _root_.GD.N0232.N0720.N1316.d004440 k) :
    Measurable (_root_.GD.N0232.N0720.N1316.d004445 q) := by
  unfold _root_.GD.N0232.N0720.N1316.d004445
  fun_prop



theorem d019897 (q : _root_.GD.N0232.N0720.N1329.d019646) (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    (∫⁻ omega, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h omega - q.1) ^ 2)
      ∂_root_.GD.N0107.d009030 m n q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q)) =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim q h) := by
  let p := _root_.GD.N0232.N0720.N1329.d019660 m n k hdim q
  have hm : Measurable (fun x : _root_.GD.N0232.N0720.N1341.d004414 k ↦
      ENNReal.ofReal ((_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2)) :=
    ((_root_.GD.N0232.N0720.N1326.d019885 h).sub measurable_const).pow_const 2 |>.ennreal_ofReal
  calc
    _ = ∫⁻ x, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2)
        ∂volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004445 p x)) :=
      _root_.GD.N0232.N0720.N1329.d019670 m n k hdim q _ (_root_.GD.N0232.N0720.N1326.d019885 h)
    _ = ∫⁻ x, ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004445 p x) *
        ENNReal.ofReal ((_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2) :=
      lintegral_withDensity_eq_lintegral_mul volume
        (_root_.GD.N0232.N0720.N1326.d019896 k p).ennreal_ofReal hm
    _ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim q h) := by
      change _ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004469 p h)
      rw [_root_.GD.N0232.N0720.N1316.d004469,
        ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0232.N0720.N1316.d004468 p h)
          (ae_of_all _ (fun x ↦ mul_nonneg (sq_nonneg _)
            (_root_.GD.N0232.N0720.N1326.d019895 k p x)))]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (_root_.GD.N0232.N0720.N1326.d019895 k p x), mul_comm]
      rfl

def d019898 (c : ℝ) : _root_.GD.N0232.N0720.N1329.d019645 m n → _root_.GD.N0232.N0720.N1329.d019645 m n :=
  _root_.GD.N0107.d009024 m n 0 c c

@[fun_prop]
theorem d019899 (c : ℝ) : Measurable (_root_.GD.N0232.N0720.N1326.d019898 m n c) :=
  _root_.GD.N0107.d009026 m n 0 c c

theorem d019900 (mu sigma tau c : ℝ) :
    (_root_.GD.N0107.d009030 m n mu sigma tau).map (_root_.GD.N0232.N0720.N1326.d019898 m n c) =
      _root_.GD.N0107.d009030 m n (c * mu) (c * sigma) (c * tau) := by
  unfold _root_.GD.N0107.d009030
  rw [Measure.map_map (_root_.GD.N0232.N0720.N1326.d019899 m n c)
    (_root_.GD.N0107.d009026 m n mu sigma tau)]
  congr 1
  funext x
  apply Prod.ext <;> funext i <;>
    simp only [Function.comp_apply, _root_.GD.N0232.N0720.N1326.d019898, _root_.GD.N0107.d009024, _root_.GD.N0107.d009018, zero_add] <;>
    ring

theorem d019901 (c : ℝ) (omega : _root_.GD.N0232.N0720.N1329.d019645 m n) :
    _root_.GD.N0232.N0720.N1329.d019648 m n k hdim (_root_.GD.N0232.N0720.N1326.d019898 m n c omega) = c • _root_.GD.N0232.N0720.N1329.d019648 m n k hdim omega := by
  apply (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm.injective
  rw [(_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm_apply_apply, _root_.GD.N0232.N0720.N1329.d019652,
    (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm_apply_apply]
  apply Prod.ext
  · funext i
    change 0 + c * omega.1 i = c * omega.1 i
    exact zero_add _
  · funext i
    change 0 + c * omega.2 i = c * omega.2 i
    exact zero_add _

theorem d019902 (h : _root_.GD.N0232.N0720.N1341.d004417 k) {c : ℝ} (hc : 0 < c)
    (omega : _root_.GD.N0232.N0720.N1329.d019645 m n) :
    _root_.GD.N0232.N0720.N1326.d019893 m n k hdim h (_root_.GD.N0232.N0720.N1326.d019898 m n c omega) = c * _root_.GD.N0232.N0720.N1326.d019893 m n k hdim h omega := by
  unfold _root_.GD.N0232.N0720.N1326.d019893
  rw [_root_.GD.N0232.N0720.N1326.d019901]
  simpa only [smul_eq_mul] using
    _root_.GD.N0232.N0720.N1341.d004419 h c hc (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim omega)

theorem d019903 (h : _root_.GD.N0232.N0720.N1341.d004417 k) (mu sigma tau : ℝ)
    {c : ℝ} (hc : 0 < c) :
    (∫⁻ omega, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h omega - c * mu) ^ 2)
      ∂_root_.GD.N0107.d009030 m n (c * mu) (c * sigma) (c * tau)) =
    ENNReal.ofReal (c ^ 2) *
      ∫⁻ omega, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h omega - mu) ^ 2)
        ∂_root_.GD.N0107.d009030 m n mu sigma tau := by
  rw [← _root_.GD.N0232.N0720.N1326.d019900,
    lintegral_map (by fun_prop) (_root_.GD.N0232.N0720.N1326.d019899 m n c)]
  simp_rw [_root_.GD.N0232.N0720.N1326.d019902 m n k hdim h hc,
    ← mul_sub, mul_pow, ENNReal.ofReal_mul (sq_nonneg c)]
  exact lintegral_const_mul _ (by fun_prop)

def d019904 (theta : _root_.GD.N0232.N0720.N1326.d019882) : ℝ := theta.scale₁ ^ 2 + theta.scale₂ ^ 2

theorem d019905 (theta : _root_.GD.N0232.N0720.N1326.d019882) : 0 < _root_.GD.N0232.N0720.N1326.d019904 theta :=
  add_pos (sq_pos_of_pos theta.scale₁_pos) (sq_pos_of_pos theta.scale₂_pos)


def d019906 (theta : _root_.GD.N0232.N0720.N1326.d019882) : ℝ := Real.sqrt (_root_.GD.N0232.N0720.N1326.d019904 theta)

theorem d019907 (theta : _root_.GD.N0232.N0720.N1326.d019882) : 0 < _root_.GD.N0232.N0720.N1326.d019906 theta :=
  Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1326.d019905 theta)

theorem d019908 (theta : _root_.GD.N0232.N0720.N1326.d019882) : _root_.GD.N0232.N0720.N1326.d019906 theta ^ 2 = _root_.GD.N0232.N0720.N1326.d019904 theta :=
  Real.sq_sqrt (_root_.GD.N0232.N0720.N1326.d019905 theta).le

def d019909 (theta : _root_.GD.N0232.N0720.N1326.d019882) : Ioo (0 : ℝ) 1 :=
  ⟨theta.scale₁ ^ 2 / _root_.GD.N0232.N0720.N1326.d019904 theta,
    div_pos (sq_pos_of_pos theta.scale₁_pos) (_root_.GD.N0232.N0720.N1326.d019905 theta),
    (div_lt_one (_root_.GD.N0232.N0720.N1326.d019905 theta)).2 (by
      unfold _root_.GD.N0232.N0720.N1326.d019904
      linarith [sq_pos_of_pos theta.scale₂_pos])⟩

def d019910 (theta : _root_.GD.N0232.N0720.N1326.d019882) : _root_.GD.N0232.N0720.N1329.d019646 :=
  (theta.location / _root_.GD.N0232.N0720.N1326.d019906 theta, _root_.GD.N0232.N0720.N1326.d019909 theta)

theorem d019911 (theta : _root_.GD.N0232.N0720.N1326.d019882) :
    _root_.GD.N0232.N0720.N1326.d019906 theta * (_root_.GD.N0232.N0720.N1326.d019910 theta).1 = theta.location :=
  mul_div_cancel₀ _ (_root_.GD.N0232.N0720.N1326.d019907 theta).ne'

theorem d019912 (theta : _root_.GD.N0232.N0720.N1326.d019882) :
    _root_.GD.N0232.N0720.N1326.d019906 theta * _root_.GD.N0232.N0720.N1329.d019663 (_root_.GD.N0232.N0720.N1326.d019910 theta) = theta.scale₁ := by
  apply (sq_eq_sq₀ (mul_pos (_root_.GD.N0232.N0720.N1326.d019907 theta) (_root_.GD.N0232.N0720.N1329.d019665 _)).le
    theta.scale₁_pos.le).mp
  rw [mul_pow, _root_.GD.N0232.N0720.N1326.d019908]
  unfold _root_.GD.N0232.N0720.N1329.d019663
  rw [Real.sq_sqrt (_root_.GD.N0232.N0720.N1326.d019910 theta).2.2.1.le]
  change _root_.GD.N0232.N0720.N1326.d019904 theta * (theta.scale₁ ^ 2 / _root_.GD.N0232.N0720.N1326.d019904 theta) = theta.scale₁ ^ 2
  exact mul_div_cancel₀ _ (_root_.GD.N0232.N0720.N1326.d019905 theta).ne'

theorem d019913 (theta : _root_.GD.N0232.N0720.N1326.d019882) :
    _root_.GD.N0232.N0720.N1326.d019906 theta * _root_.GD.N0232.N0720.N1329.d019664 (_root_.GD.N0232.N0720.N1326.d019910 theta) = theta.scale₂ := by
  apply (sq_eq_sq₀ (mul_pos (_root_.GD.N0232.N0720.N1326.d019907 theta) (_root_.GD.N0232.N0720.N1329.d019666 _)).le
    theta.scale₂_pos.le).mp
  rw [mul_pow, _root_.GD.N0232.N0720.N1326.d019908]
  unfold _root_.GD.N0232.N0720.N1329.d019664
  rw [Real.sq_sqrt (sub_pos.mpr (_root_.GD.N0232.N0720.N1326.d019910 theta).2.2.2).le]
  change _root_.GD.N0232.N0720.N1326.d019904 theta * (1 - theta.scale₁ ^ 2 / _root_.GD.N0232.N0720.N1326.d019904 theta) =
    theta.scale₂ ^ 2
  field_simp [(_root_.GD.N0232.N0720.N1326.d019905 theta).ne']
  dsimp [_root_.GD.N0232.N0720.N1326.d019904]
  ring


theorem d019914 (theta : _root_.GD.N0232.N0720.N1326.d019882) (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h) =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1326.d019906 theta ^ 2) *
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim (_root_.GD.N0232.N0720.N1326.d019910 theta) h) := by
  have hr := _root_.GD.N0232.N0720.N1326.d019903 m n k hdim h (_root_.GD.N0232.N0720.N1326.d019910 theta).1
    (_root_.GD.N0232.N0720.N1329.d019663 (_root_.GD.N0232.N0720.N1326.d019910 theta)) (_root_.GD.N0232.N0720.N1329.d019664 (_root_.GD.N0232.N0720.N1326.d019910 theta))
    (_root_.GD.N0232.N0720.N1326.d019907 theta)
  rw [_root_.GD.N0232.N0720.N1326.d019911, _root_.GD.N0232.N0720.N1326.d019912, _root_.GD.N0232.N0720.N1326.d019913,
    _root_.GD.N0232.N0720.N1326.d019897] at hr
  exact hr

def d019915 (q : _root_.GD.N0232.N0720.N1329.d019646) : _root_.GD.N0232.N0720.N1326.d019882 where
  location := q.1
  scale₁ := _root_.GD.N0232.N0720.N1329.d019663 q
  scale₂ := _root_.GD.N0232.N0720.N1329.d019664 q
  scale₁_pos := _root_.GD.N0232.N0720.N1329.d019665 q
  scale₂_pos := _root_.GD.N0232.N0720.N1329.d019666 q

theorem d019916 (q : _root_.GD.N0232.N0720.N1329.d019646) (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    _root_.GD.N0232.N0720.N1080.d014197 m n (_root_.GD.N0232.N0720.N1326.d019915 q)
      (_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h) = ENNReal.ofReal (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim q h) :=
  _root_.GD.N0232.N0720.N1326.d019897 m n k hdim q h

theorem d019917 (q : _root_.GD.N0232.N0720.N1329.d019646) (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    0 ≤ _root_.GD.N0232.N0720.N1326.d019892 m n k hdim q h := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (sq_nonneg _) (_root_.GD.N0232.N0720.N1326.d019895 k _ x)



theorem d019918 (h : _root_.GD.N0232.N0720.N1341.d004417 k)
    (hraw : ¬ ∃ d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ, Measurable d ∧
      (∀ theta : _root_.GD.N0232.N0720.N1326.d019882, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h)) ∧
      ∃ theta : _root_.GD.N0232.N0720.N1326.d019882, _root_.GD.N0232.N0720.N1080.d014197 m n theta d <
        _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h)) :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim) h := by
  rintro ⟨g, hweak, q, hstrict⟩
  apply hraw
  refine ⟨_root_.GD.N0232.N0720.N1326.d019893 m n k hdim g, _root_.GD.N0232.N0720.N1326.d019894 m n k hdim g, ?_, ?_⟩
  · intro theta
    rw [_root_.GD.N0232.N0720.N1326.d019914, _root_.GD.N0232.N0720.N1326.d019914]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hweak _)) _
  · refine ⟨_root_.GD.N0232.N0720.N1326.d019915 q, ?_⟩
    rw [_root_.GD.N0232.N0720.N1326.d019916, _root_.GD.N0232.N0720.N1326.d019916]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (_root_.GD.N0232.N0720.N1326.d019917 m n k hdim q g)).2 hstrict



theorem d019919 {f g : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ} (hfg : f =ᵐ[volume] g)
    (theta : _root_.GD.N0232.N0720.N1326.d019882) :
    f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      g ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim := by
  let q : _root_.GD.N0232.N0720.N1329.d019646 := (0, ⟨1 / 2, by norm_num, by norm_num⟩)
  have hq : Measure.QuasiMeasurePreserving (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim)
      (_root_.GD.N0107.d009030 m n q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q)) volume := by
    refine ⟨(_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).measurable, ?_⟩
    rw [_root_.GD.N0232.N0720.N1329.d019669]
    exact withDensity_absolutelyContinuous _ _
  have hac : _root_.GD.N0232.N0720.N1080.d014171 m n theta ≪
      _root_.GD.N0107.d009030 m n q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q) :=
    _root_.GD.N0232.N0720.d009062 m n theta.location theta.scale₁ theta.scale₂
      q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q) theta.scale₁_pos.ne' theta.scale₂_pos.ne'
      (_root_.GD.N0232.N0720.N1329.d019665 q).ne' (_root_.GD.N0232.N0720.N1329.d019666 q).ne'
  exact hac.ae_le (hq.ae_eq_comp hfg)

theorem d019920 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f)
    (hhom : _root_.GD.N0238.N0753.d004397 f) (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ C)
    (theta : _root_.GD.N0232.N0720.N1326.d019882) :
    _root_.GD.N0232.N0720.N1326.d019893 m n k hdim (_root_.GD.N0232.N0720.N1326.d019889 f hf C hbound) =ᵐ[
      _root_.GD.N0232.N0720.N1080.d014171 m n theta] f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim :=
  _root_.GD.N0232.N0720.N1326.d019919 m n k hdim (_root_.GD.N0232.N0720.N1326.d019891 f hf hhom C hbound) theta

theorem d019921
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f) (hhom : _root_.GD.N0238.N0753.d004397 f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ C)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
      f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim) (_root_.GD.N0232.N0720.N1326.d019889 f hf C hbound) := by
  let h := _root_.GD.N0232.N0720.N1326.d019889 f hf C hbound
  have heq : ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
      _root_.GD.N0232.N0720.N1326.d019893 m n k hdim h =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d :=
    fun theta ↦ (_root_.GD.N0232.N0720.N1326.d019920 m n k hdim f hf hhom C hbound theta).trans
      (hrep theta)
  have hrisk : ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h) =
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d :=
    fun theta ↦ _root_.GD.N0232.N0720.N1159.d014662 m n theta (heq theta)
  apply _root_.GD.N0232.N0720.N1326.d019918
  rintro ⟨e, he, hweak, theta, hstrict⟩
  have hterm := hd.2.2.2 e he (fun q ↦ (hweak q).trans (hrisk q).le) theta
  have heRisk := _root_.GD.N0232.N0720.N1159.d014662 m n theta hterm
  rw [heRisk, hrisk theta] at hstrict
  exact lt_irrefl _ hstrict



theorem d019922 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 k, _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim) h ∧
      ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
        _root_.GD.N0232.N0720.N1326.d019893 m n k hdim h =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d := by
  obtain ⟨g, hg, hb, hae⟩ :=
    _root_.GD.N0232.N0720.N1342.d019642 m n hm hn hd
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  let f := _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g
  have hf : Measurable f := _root_.GD.N0232.N0720.N1329.d019672 m n k hdim hg
  have hhom : _root_.GD.N0238.N0753.d004397 f :=
    _root_.GD.N0232.N0720.N1329.d019675 m n k hdim hm0 hn0 g
  have hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ 1 :=
    _root_.GD.N0232.N0720.N1329.d019679 m n k hdim hm0 hn0 hb
  have hrep : ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
      f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d := by
    intro theta
    simpa only [Function.comp_def, f, _root_.GD.N0232.N0720.N1329.d019673] using (hae theta).symm
  refine ⟨_root_.GD.N0232.N0720.N1326.d019889 f hf 1 hbound, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1326.d019921 m n k hdim hd f hf hhom 1 hbound hrep
  · intro theta
    exact (_root_.GD.N0232.N0720.N1326.d019920 m n k hdim f hf hhom 1 hbound theta).trans (hrep theta)

end

end GD.N0232.N0720.N1326

#print axioms _root_.GD.N0232.N0720.N1326.d019886
#print axioms _root_.GD.N0232.N0720.N1326.d019897
#print axioms _root_.GD.N0232.N0720.N1326.d019914
#print axioms _root_.GD.N0232.N0720.N1326.d019919
#print axioms _root_.GD.N0232.N0720.N1326.d019922
