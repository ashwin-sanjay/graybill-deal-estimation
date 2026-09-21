import GD.Module0320
import Mathlib.LinearAlgebra.Quotient.Basic

























namespace GD
namespace N0233
namespace N0724

noncomputable section

open _root_.GD.N0234.N0738

variable {V ι : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable {W : ι → Type*}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]


def d004785 (detector : ∀ i, V →ₗ[ℝ] W i) : Submodule ℝ V :=
  ⨅ i, LinearMap.ker (detector i)

@[simp]
theorem d004786
    (detector : ∀ i, V →ₗ[ℝ] W i) (x : V) :
    x ∈ _root_.GD.N0233.N0724.d004785 detector ↔ ∀ i, detector i x = 0 := by
  simp [_root_.GD.N0233.N0724.d004785]


def d004787
    (detector : ∀ i, V →ₗ[ℝ] W i) :
    V →ₗ[ℝ] (∀ i, W i) :=
  LinearMap.pi detector

@[simp]
theorem d004788
    (detector : ∀ i, V →ₗ[ℝ] W i) (x : V) (i : ι) :
    _root_.GD.N0233.N0724.d004787 detector x i = detector i x :=
  rfl


theorem d004789
    (detector : ∀ i, V →ₗ[ℝ] W i) :
    LinearMap.ker (_root_.GD.N0233.N0724.d004787 detector) = _root_.GD.N0233.N0724.d004785 detector := by
  simpa [_root_.GD.N0233.N0724.d004787, _root_.GD.N0233.N0724.d004785] using
    (LinearMap.ker_pi detector)


theorem d004790
    (gauge : Submodule ℝ V)
    (detector : ∀ i, V →ₗ[ℝ] W i) :
    gauge ≤ _root_.GD.N0233.N0724.d004785 detector ↔
      ∀ i, gauge ≤ LinearMap.ker (detector i) := by
  simp [_root_.GD.N0233.N0724.d004785]





def d004791
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (gauge : Submodule ℝ V) (A : V →ₗ[ℝ] Y)
    (hgauge : gauge ≤ LinearMap.ker A) :
    (V ⧸ gauge) →ₗ[ℝ] Y :=
  gauge.liftQ A hgauge

@[simp]
theorem d004792
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (gauge : Submodule ℝ V) (A : V →ₗ[ℝ] Y)
    (hgauge : gauge ≤ LinearMap.ker A) (x : V) :
    _root_.GD.N0233.N0724.d004791 gauge A hgauge (gauge.mkQ x) = A x :=
  rfl





theorem d004793
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (gauge : Submodule ℝ V) (A : V →ₗ[ℝ] Y)
    (hgauge : gauge ≤ LinearMap.ker A) :
    LinearMap.ker A = gauge ↔
      Function.Injective (_root_.GD.N0233.N0724.d004791 gauge A hgauge) := by
  constructor
  · intro hkernel
    apply LinearMap.ker_eq_bot.mp
    exact
      Submodule.ker_liftQ_eq_bot
        gauge A hgauge hkernel.le
  · intro hinjective
    apply le_antisymm
    · intro x hx
      rw [← Submodule.Quotient.mk_eq_zero]
      apply hinjective
      change A x = A 0
      simpa using hx
    · exact hgauge


def d004794
    (gauge : Submodule ℝ V)
    (detector : ∀ i, V →ₗ[ℝ] W i)
    (hgauge : gauge ≤ _root_.GD.N0233.N0724.d004785 detector) :
    (V ⧸ gauge) →ₗ[ℝ] (∀ i, W i) :=
  _root_.GD.N0233.N0724.d004791 gauge (_root_.GD.N0233.N0724.d004787 detector) <| by
    simpa only [_root_.GD.N0233.N0724.d004789] using hgauge

@[simp]
theorem d004795
    (gauge : Submodule ℝ V)
    (detector : ∀ i, V →ₗ[ℝ] W i)
    (hgauge : gauge ≤ _root_.GD.N0233.N0724.d004785 detector)
    (x : V) (i : ι) :
    _root_.GD.N0233.N0724.d004794 gauge detector hgauge
        (gauge.mkQ x) i =
      detector i x :=
  rfl





theorem d004796
    (gauge : Submodule ℝ V)
    (detector : ∀ i, V →ₗ[ℝ] W i)
    (hgauge : gauge ≤ _root_.GD.N0233.N0724.d004785 detector) :
    _root_.GD.N0233.N0724.d004785 detector = gauge ↔
      Function.Injective
        (_root_.GD.N0233.N0724.d004794 gauge detector hgauge) := by
  unfold _root_.GD.N0233.N0724.d004794
  rw [← _root_.GD.N0233.N0724.d004789 detector]
  exact
    _root_.GD.N0233.N0724.d004793
      gauge (_root_.GD.N0233.N0724.d004787 detector)
      (by simpa only [_root_.GD.N0233.N0724.d004789] using hgauge)





theorem d004797
    (gauge : Submodule ℝ V)
    (detector : ∀ i, V →ₗ[ℝ] W i)
    (hgauge : gauge ≤ _root_.GD.N0233.N0724.d004785 detector) :
    _root_.GD.N0233.N0724.d004785 detector = gauge ↔
      ∀ x y : V,
        (∀ i, detector i x = detector i y) ↔ x - y ∈ gauge := by
  constructor
  · intro hcomplete x y
    constructor
    · intro hsame
      rw [← hcomplete]
      rw [_root_.GD.N0233.N0724.d004786]
      intro i
      simpa only [map_sub, sub_eq_zero] using hsame i
    · intro hxy i
      have hcommon : x - y ∈ _root_.GD.N0233.N0724.d004785 detector := by
        rw [hcomplete]
        exact hxy
      have hi := (_root_.GD.N0233.N0724.d004786 detector (x - y)).mp hcommon i
      simpa only [map_sub, sub_eq_zero] using hi
  · intro hsame
    apply le_antisymm
    · intro x hx
      have hxzero : ∀ i, detector i x = detector i 0 := by
        intro i
        simpa using (_root_.GD.N0233.N0724.d004786 detector x).mp hx i
      have := (hsame x 0).mp hxzero
      simpa using this
    · exact hgauge








def d004798
    (s : Finset ι) (detector : ∀ i, V →ₗ[ℝ] W i) :
    V →ₗ[ℝ] (∀ i : ↥s, W i.1) :=
  LinearMap.pi fun i : ↥s ↦ detector i.1

@[simp]
theorem d004799
    (s : Finset ι) (detector : ∀ i, V →ₗ[ℝ] W i)
    (x : V) (i : ↥s) :
    _root_.GD.N0233.N0724.d004798 s detector x i = detector i.1 x :=
  rfl

@[simp]
theorem d004800
    (s : Finset ι) (detector : ∀ i, V →ₗ[ℝ] W i)
    (x : V) :
    x ∈ LinearMap.ker (_root_.GD.N0233.N0724.d004798 s detector) ↔
      ∀ i ∈ s, detector i x = 0 := by
  constructor
  · intro hx i hi
    have hfun :
        _root_.GD.N0233.N0724.d004798 s detector x = 0 :=
      hx
    have := congrFun hfun ⟨i, hi⟩
    simpa using this
  · intro hx
    change _root_.GD.N0233.N0724.d004798 s detector x = 0
    funext i
    exact hx i.1 i.2


theorem d004801
    (s : Finset ι) (detector : ∀ i, V →ₗ[ℝ] W i) :
    LinearMap.ker (_root_.GD.N0233.N0724.d004798 s detector) =
      ⨅ i, ⨅ _ : i ∈ s, LinearMap.ker (detector i) := by
  ext x
  constructor
  · intro hx
    have hselected :=
      (_root_.GD.N0233.N0724.d004800 s detector x).mp hx
    simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hselected
  · intro hx
    apply (_root_.GD.N0233.N0724.d004800 s detector x).mpr
    simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hx

variable [FiniteDimensional ℝ V]






theorem d004802
    (detector : ∀ i, V →ₗ[ℝ] W i) :
    ∃ s : Finset ι,
      s.card + Module.finrank ℝ (_root_.GD.N0233.N0724.d004785 detector) ≤
          Module.finrank ℝ V ∧
      LinearMap.ker (_root_.GD.N0233.N0724.d004798 s detector) =
        _root_.GD.N0233.N0724.d004785 detector := by
  obtain ⟨s, hcard, hkernel⟩ :=
    _root_.GD.N0234.N0738.d004779
      (fun i ↦ LinearMap.ker (detector i))
  refine ⟨s, ?_, ?_⟩
  · have hdef :
        _root_.GD.N0233.N0724.d004785 detector =
          ⨅ i : ι, LinearMap.ker (detector i) := rfl
    rw [hdef]
    exact hcard
  · rw [_root_.GD.N0233.N0724.d004801, hkernel]
    rfl









theorem d004803
    (gauge : Submodule ℝ V)
    (detector : ∀ i, V →ₗ[ℝ] W i)
    (hgauge : gauge ≤ _root_.GD.N0233.N0724.d004785 detector) :
    _root_.GD.N0233.N0724.d004785 detector = gauge ↔
      ∃ s : Finset ι,
        s.card + Module.finrank ℝ gauge ≤ Module.finrank ℝ V ∧
        LinearMap.ker (_root_.GD.N0233.N0724.d004798 s detector) = gauge := by
  constructor
  · intro hcomplete
    obtain ⟨s, hcard, hkernel⟩ :=
      _root_.GD.N0233.N0724.d004802 detector
    refine ⟨s, ?_, ?_⟩
    · rw [hcomplete] at hcard
      exact hcard
    · simpa [hcomplete] using hkernel
  · rintro ⟨s, hcard, hkernel⟩
    apply le_antisymm
    · intro x hx
      rw [← hkernel]
      rw [_root_.GD.N0233.N0724.d004800]
      intro i hi
      exact (_root_.GD.N0233.N0724.d004786 detector x).mp hx i
    · exact hgauge








theorem d004804
    (gauge : Submodule ℝ V)
    (detector : ∀ i, V →ₗ[ℝ] W i)
    (hgauge : gauge ≤ _root_.GD.N0233.N0724.d004785 detector) :
    (∃ x : V, x ∈ _root_.GD.N0233.N0724.d004785 detector ∧ x ∉ gauge) ∨
      ∃ s : Finset ι,
        s.card + Module.finrank ℝ gauge ≤ Module.finrank ℝ V ∧
        LinearMap.ker (_root_.GD.N0233.N0724.d004798 s detector) = gauge := by
  by_cases hcomplete : _root_.GD.N0233.N0724.d004785 detector = gauge
  · exact Or.inr <|
      (_root_.GD.N0233.N0724.d004803
        gauge detector hgauge).mp hcomplete
  · left
    have hstrict : gauge < _root_.GD.N0233.N0724.d004785 detector :=
      lt_of_le_of_ne hgauge (Ne.symm hcomplete)
    obtain ⟨x, hxcommon, hxgauge⟩ :=
      SetLike.exists_of_lt hstrict
    exact ⟨x, hxcommon, hxgauge⟩

end

end N0724
end N0233
end GD
