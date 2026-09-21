import GD.Module0806
import GD.Module0631







set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal
namespace GD.N0232.N0719.N0972
noncomputable section
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0843 _root_.GD.N0232.N0719.N0844
open _root_.GD.N0232.N0719.N0962 (d012190 d012191)
open _root_.GD.N0230.N0611
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (k : ℕ) (sizes : Fin k → ℕ)

def d012340 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
    (fun omega ↦ _root_.GD.N0232.N0719.N0859.d010815 k sizes omega - theta.location)

theorem d012341 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes theta) := by
  rw [_root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0859.d010823 k sizes hk hsizes]
  rfl

theorem d012342 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : 0 < _root_.GD.N0232.N0719.N0972.d012340 k sizes theta := by
  apply ENNReal.ofReal_pos.mp
  have h := (_root_.GD.N0232.N0719.N0858.d010854 k sizes hk hsizes theta).trans
    (_root_.GD.N0232.N0719.N0858.d010856 k sizes hk hsizes theta)
  simpa only [_root_.GD.N0232.N0719.N0859.d010823 k sizes hk hsizes, _root_.GD.N0232.N0719.N0972.d012340] using h

def d012343 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : _root_.GD.N0232.N0719.N0843.d012215 k where
  value := _root_.GD.N0232.N0719.N0972.d012340 k sizes
  positive := _root_.GD.N0232.N0719.N0972.d012342 k sizes hk hsizes
  character g theta := by
    exact _root_.GD.N0232.N0719.N0804.d009189 k sizes
      (by omega) (fun i ↦ by have := hsizes i; omega)
      g.shift theta.location g.d009239 (ne_of_gt g.d009240) theta.scale

def d012344 (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i) : _root_.GD.N0232.N0719.N0843.d012215 k where
  value := _root_.GD.N0232.N0719.N0963.d012141 k sizes
  positive := _root_.GD.N0232.N0719.N0963.d012143 k sizes hk hsizes
  character := _root_.GD.N0232.N0719.N0963.d012145 k sizes


def d012345 (gamma eta : _root_.GD.N0232.N0719.N0843.d012215 k) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    _root_.GD.N0232.N0719.N0843.d012215 k where
  value theta := min (a * gamma.value theta) (b * eta.value theta)
  positive theta := lt_min (mul_pos ha (gamma.positive theta)) (mul_pos hb (eta.positive theta))
  character g theta := by
    rw [gamma.character, eta.character]
    calc
      min (a * (g.d009239 ^ 2 * gamma.value theta))
          (b * (g.d009239 ^ 2 * eta.value theta)) =
        min (g.d009239 ^ 2 * (a * gamma.value theta))
          (g.d009239 ^ 2 * (b * eta.value theta)) := by ring_nf
      _ = _ := (mul_min_of_nonneg _ _ (sq_nonneg g.d009239)).symm

theorem d012346 (gamma eta : _root_.GD.N0232.N0719.N0843.d012215 k) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes (_root_.GD.N0232.N0719.N0972.d012345 k gamma eta a b ha hb) 1 ↔
      p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes gamma a ∧
      p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes eta b := by
  simp only [_root_.GD.N0232.N0719.N0843.d012216, _root_.GD.N0232.N0719.N0972.d012345, Set.mem_setOf_eq, one_mul,
    ENNReal.ofReal_min, le_min_iff]
  exact forall_and

theorem d012347 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) theta
      (_root_.GD.N0232.N0719.N0859.d010815 k sizes) = 1 := by
  unfold _root_.GD.N0232.N0719.N0844.d012246
  rw [_root_.GD.N0232.N0719.N0972.d012341 k sizes hk hsizes]
  exact ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.mpr
    (_root_.GD.N0232.N0719.N0972.d012342 k sizes hk hsizes theta))) ENNReal.ofReal_ne_top

theorem d012348 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0844.d012247 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0859.d010815 k sizes) = 1 := by
  haveI : Nonempty (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨_root_.GD.N0232.N0719.N0859.d010810 k⟩
  simp [_root_.GD.N0232.N0719.N0844.d012247, _root_.GD.N0230.N0611.d003516, _root_.GD.N0232.N0719.N0972.d012347 k sizes hk hsizes]

theorem d012349 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) ≤ 1 := by
  calc
    _root_.GD.N0232.N0719.N0844.d012248 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) ≤
      _root_.GD.N0232.N0719.N0844.d012247 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d010815 k sizes) :=
      _root_.GD.N0230.N0611.d003520 _ (_root_.GD.N0232.N0719.N0900.d009122 k sizes)
    _ = 1 := _root_.GD.N0232.N0719.N0972.d012348 k sizes hk hsizes



theorem d012350 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      _root_.GD.N0232.N0719.N0844.d012247 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes))
          (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ∧
      _root_.GD.N0232.N0719.N0844.d012247 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes))
          (_root_.GD.N0232.N0719.N0962.d012191 k sizes) ∧
      _root_.GD.N0232.N0719.N0844.d012247 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) e ≤ 1 := by
  obtain ⟨e, he, hD, hvD, hvE⟩ :=
    _root_.GD.N0232.N0719.N0844.d012264 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) hk hsizes
  refine ⟨e, he, hD, hvD, hvE, ?_⟩
  rw [hvD, ← _root_.GD.N0232.N0719.N0844.d012256 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) hk hsizes]
  exact _root_.GD.N0232.N0719.N0972.d012349 k sizes hk hsizes

end
end GD.N0232.N0719.N0972
#print axioms _root_.GD.N0232.N0719.N0972.d012342
#print axioms _root_.GD.N0232.N0719.N0972.d012346
#print axioms _root_.GD.N0232.N0719.N0972.d012350
