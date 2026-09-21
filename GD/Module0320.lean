import GD.Module0319
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
























open Matrix Set
open scoped BigOperators MatrixOrder

namespace GD
namespace N0234
namespace N0738

noncomputable section

open _root_.GD.N0234.N0742

variable {V ι n X : Type*}
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [Fintype n] [DecidableEq n]


def d004776 (K : ι → Submodule ℝ V) :
    Submodule ℝ V → List ι → Submodule ℝ V
  | L, [] => L
  | L, i :: l => d004776 K (L ⊓ K i) l



theorem d004777
    (K : ι → Submodule ℝ V) (L : Submodule ℝ V)
    (l : List ι) (v : V) :
    v ∈ _root_.GD.N0234.N0738.d004776 K L l ↔
      v ∈ L ∧ ∀ i ∈ l, v ∈ K i := by
  induction l generalizing L with
  | nil =>
      simp [_root_.GD.N0234.N0738.d004776]
  | cons i l ih =>
      simp only [_root_.GD.N0234.N0738.d004776, ih, Submodule.mem_inf, List.mem_cons]
      aesop







theorem d004778
    (K : ι → Submodule ℝ V) (L : Submodule ℝ V)
    (hglobal : (⨅ i, K i) ≤ L) :
    ∃ l : List ι,
      _root_.GD.N0234.N0738.d004776 K L l = ⨅ i, K i ∧
      l.length + Module.finrank ℝ ↥(⨅ i, K i) ≤
        Module.finrank ℝ L := by
  classical
  let G : Submodule ℝ V := ⨅ i, K i
  have aux :
      ∀ d : ℕ, ∀ L : Submodule ℝ V,
        Module.finrank ℝ L = d → G ≤ L →
        ∃ l : List ι,
          _root_.GD.N0234.N0738.d004776 K L l = G ∧
          l.length + Module.finrank ℝ G ≤
            Module.finrank ℝ L := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro L hdim hGL
        by_cases hLG : L = G
        · subst L
          refine ⟨[], rfl, ?_⟩
          simp
        · have hGLlt : G < L :=
            lt_of_le_of_ne hGL (Ne.symm hLG)
          obtain ⟨v, hvL, hvG⟩ := SetLike.exists_of_lt hGLlt
          have hnotall : ¬ ∀ i, v ∈ K i := by
            intro hall
            apply hvG
            simpa [G] using hall
          push Not at hnotall
          obtain ⟨i, hi⟩ := hnotall
          let L' : Submodule ℝ V := L ⊓ K i
          have hGL' : G ≤ L' := by
            refine le_inf hGL ?_
            exact iInf_le K i
          have hL'lt : L' < L := by
            refine lt_of_le_of_ne inf_le_left ?_
            intro heq
            have hvL' : v ∈ L' := by
              rw [heq]
              exact hvL
            exact hi hvL'.2
          have hdimlt :
              Module.finrank ℝ L' < Module.finrank ℝ L :=
            Submodule.finrank_lt_finrank_of_lt hL'lt
          have hdimd : Module.finrank ℝ L' < d := by
            simpa [hdim] using hdimlt
          obtain ⟨l, hlcut, hllen⟩ :=
            ih (Module.finrank ℝ L') hdimd L' rfl hGL'
          refine ⟨i :: l, ?_, ?_⟩
          · simpa [_root_.GD.N0234.N0738.d004776, L'] using hlcut
          · have hstep :
                Module.finrank ℝ L' + 1 ≤ Module.finrank ℝ L :=
              Nat.succ_le_iff.mpr hdimlt
            simp only [List.length_cons]
            omega
  simpa [G] using aux (Module.finrank ℝ L) L rfl hglobal







theorem d004779
    (K : ι → Submodule ℝ V) :
    ∃ s : Finset ι,
      s.card + Module.finrank ℝ ↥(⨅ i, K i) ≤
        Module.finrank ℝ V ∧
      (⨅ i ∈ s, K i) = ⨅ i, K i := by
  classical
  obtain ⟨l, hlcut, hllen⟩ :=
    _root_.GD.N0234.N0738.d004778 K (⊤ : Submodule ℝ V) (by simp)
  refine ⟨l.toFinset, ?_, ?_⟩
  · calc
      l.toFinset.card + Module.finrank ℝ ↥(⨅ i, K i)
          ≤ l.length + Module.finrank ℝ ↥(⨅ i, K i) :=
        Nat.add_le_add_right l.toFinset_card_le _
      _ ≤ Module.finrank ℝ (⊤ : Submodule ℝ V) := hllen
      _ = Module.finrank ℝ V := by simp
  · ext v
    have hmem := _root_.GD.N0234.N0738.d004777 K
      (⊤ : Submodule ℝ V) l v
    rw [hlcut] at hmem
    simpa using hmem.symm


def d004780 (P : Matrix n n ℝ) :
    Submodule ℝ (n → ℝ) :=
  LinearMap.ker P.mulVecLin


@[simp]
theorem d004781
    (P : Matrix n n ℝ) (v : n → ℝ) :
    v ∈ _root_.GD.N0234.N0738.d004780 P ↔ P *ᵥ v = 0 :=
  Iff.rfl






theorem d004782
    (P : ι → Matrix n n ℝ) :
    ∃ s : Finset ι,
      s.card + Module.finrank ℝ
          ↥(⨅ i, _root_.GD.N0234.N0738.d004780 (P i))
          ≤ Fintype.card n ∧
      (⨅ i ∈ s, _root_.GD.N0234.N0738.d004780 (P i)) =
        ⨅ i, _root_.GD.N0234.N0738.d004780 (P i) := by
  obtain ⟨s, hcard, hker⟩ :=
    _root_.GD.N0234.N0738.d004779
      (fun i ↦ _root_.GD.N0234.N0738.d004780 (P i))
  refine ⟨s, ?_, hker⟩
  simpa using hcard





theorem d004783
    (P : ι → Matrix n n ℝ)
    (hP : ∀ i, (P i).PosSemidef) :
    ∃ s : Finset ι,
      s.card + Module.finrank ℝ
          ↥(⨅ i, _root_.GD.N0234.N0738.d004780 (P i))
          ≤ Fintype.card n ∧
      _root_.GD.N0234.N0738.d004780 (∑ i ∈ s, P i) =
        ⨅ i, _root_.GD.N0234.N0738.d004780 (P i) := by
  classical
  obtain ⟨s, hcard, hcommon⟩ :=
    _root_.GD.N0234.N0738.d004782 P
  refine ⟨s, hcard, ?_⟩
  ext v
  rw [_root_.GD.N0234.N0738.d004781]
  rw [_root_.GD.N0234.N0742.d004750 s P
    (fun i _ ↦ hP i) v]
  rw [← hcommon]
  simp







theorem d004784
    (P : ι → Matrix n n ℝ)
    (hP : ∀ i, (P i).PosSemidef)
    (residual : X → n → ℝ) (S : Set X) :
    (∃ x, x ∈ S ∧ residual x ≠ 0 ∧
        ∀ i, P i *ᵥ residual x = 0) ∨
      ∃ s : Finset ι,
        s.card ≤ Fintype.card n ∧
        _root_.GD.N0234.N0742.d004745 (∑ i ∈ s, P i) residual S := by
  classical
  by_cases hnull :
      ∃ x, x ∈ S ∧ residual x ≠ 0 ∧
        ∀ i, P i *ᵥ residual x = 0
  · exact Or.inl hnull
  · right
    obtain ⟨s, hcard, hcommon⟩ :=
      _root_.GD.N0234.N0738.d004783 P hP
    refine ⟨s, (Nat.le_add_right _ _).trans hcard, ?_⟩
    intro x hx henergy
    have hsum :
        (∑ i ∈ s, P i) *ᵥ residual x = 0 :=
      (_root_.GD.N0234.N0742.d004746
        (Matrix.posSemidef_sum s (fun i _ ↦ hP i))
        (residual x)).1 henergy
    have hfull :
        ∀ i, P i *ᵥ residual x = 0 := by
      have :
          residual x ∈
            (⨅ i, _root_.GD.N0234.N0738.d004780 (P i)) := by
        rw [← hcommon]
        exact hsum
      simpa only [Submodule.mem_iInf,
        _root_.GD.N0234.N0738.d004781] using this
    by_contra hne
    exact hnull ⟨x, hx, hne, hfull⟩

end

end N0738
end N0234
end GD
