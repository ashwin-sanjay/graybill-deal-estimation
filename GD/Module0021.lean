import Mathlib




































open Finset

namespace GD
namespace N0230
namespace N0623

noncomputable section

section Divergence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]


def d000202 (dst : E → V) (flux : E → ℝ) (v : V) : ℝ :=
  ∑ e, if dst e = v then flux e else 0


def d000203 (src : E → V) (flux : E → ℝ) (v : V) : ℝ :=
  ∑ e, if src e = v then flux e else 0



def d000204
    (src dst : E → V) (flux : E → ℝ)
    (source sink : V → ℝ) (v : V) : ℝ :=
  source v + _root_.GD.N0230.N0623.d000202 dst flux v - sink v - _root_.GD.N0230.N0623.d000203 src flux v


theorem d000205 (dst : E → V) (flux : E → ℝ) :
    ∑ v, _root_.GD.N0230.N0623.d000202 dst flux v = ∑ e, flux e := by
  unfold _root_.GD.N0230.N0623.d000202
  rw [Finset.sum_comm]
  simp


theorem d000206 (src : E → V) (flux : E → ℝ) :
    ∑ v, _root_.GD.N0230.N0623.d000203 src flux v = ∑ e, flux e := by
  unfold _root_.GD.N0230.N0623.d000203
  rw [Finset.sum_comm]
  simp




theorem d000207
    (src dst : E → V) (flux : E → ℝ)
    (source sink : V → ℝ) :
    ∑ v, _root_.GD.N0230.N0623.d000204 src dst flux source sink v =
      (∑ v, source v) - ∑ v, sink v := by
  simp only [_root_.GD.N0230.N0623.d000204, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [_root_.GD.N0230.N0623.d000205, _root_.GD.N0230.N0623.d000206]
  ring



theorem d000208
    (src dst : E → V) (flux : E → ℝ)
    (source sink : V → ℝ)
    (hbalance : ∀ v, _root_.GD.N0230.N0623.d000204 src dst flux source sink v = 0) :
    ∑ v, source v = ∑ v, sink v := by
  have hsum : ∑ v, _root_.GD.N0230.N0623.d000204 src dst flux source sink v = 0 :=
    Finset.sum_eq_zero (fun v _hv ↦ hbalance v)
  rw [_root_.GD.N0230.N0623.d000207] at hsum
  exact sub_eq_zero.mp hsum

end Divergence

section RankedRecursion



structure d000209 (N : ℕ) (E : Type*) where
  src : E → Fin N
  dst : E → Fin N
  forward : ∀ e, src e < dst e

variable {N : ℕ} {E : Type*} [Fintype E]




noncomputable def d000210
    (G : _root_.GD.N0230.N0623.d000209 N E)
    (sinkCoeff sourceCoeff : Fin N → ℝ)
    (transfer : E → ℝ) : Fin N → ℝ :=
  wellFounded_lt.fix fun v previous ↦
    (sourceCoeff v + ∑ e, if h : G.dst e = v then
      transfer e * previous (G.src e)
        (by simpa [h] using G.forward e)
    else 0) / sinkCoeff v


theorem d000211
    (G : _root_.GD.N0230.N0623.d000209 N E)
    (sinkCoeff sourceCoeff : Fin N → ℝ)
    (transfer : E → ℝ) (v : Fin N) :
    _root_.GD.N0230.N0623.d000210 G sinkCoeff sourceCoeff transfer v =
      (sourceCoeff v + ∑ e, if G.dst e = v then
        transfer e * _root_.GD.N0230.N0623.d000210
          G sinkCoeff sourceCoeff transfer (G.src e)
      else 0) / sinkCoeff v := by
  unfold _root_.GD.N0230.N0623.d000210
  rw [wellFounded_lt.fix_eq]
  congr 2



theorem d000212
    (G : _root_.GD.N0230.N0623.d000209 N E)
    (sinkCoeff sourceCoeff : Fin N → ℝ)
    (transfer : E → ℝ)
    (hsink : ∀ v, 0 < sinkCoeff v)
    (hsource : ∀ v, 0 < sourceCoeff v)
    (htransfer : ∀ e, 0 < transfer e) :
    ∀ v, 0 < _root_.GD.N0230.N0623.d000210
      G sinkCoeff sourceCoeff transfer v := by
  intro v
  refine wellFounded_lt.induction
    (C := fun v : Fin N ↦
      0 < _root_.GD.N0230.N0623.d000210 G sinkCoeff sourceCoeff transfer v) v ?_
  intro v ih
  rw [_root_.GD.N0230.N0623.d000211]
  apply div_pos _ (hsink v)
  apply add_pos_of_pos_of_nonneg (hsource v)
  apply Finset.sum_nonneg
  intro e _he
  split_ifs with hedge
  · exact mul_nonneg (htransfer e).le
      (ih (G.src e) (by simpa [hedge] using G.forward e)).le
  · exact le_rfl



theorem d000213
    (G : _root_.GD.N0230.N0623.d000209 N E)
    (sinkCoeff sourceCoeff : Fin N → ℝ)
    (transfer : E → ℝ)
    (w : Fin N → ℝ)
    (hw : ∀ v, w v =
      (sourceCoeff v + ∑ e, if G.dst e = v then
        transfer e * w (G.src e) else 0) / sinkCoeff v) :
    w = _root_.GD.N0230.N0623.d000210 G sinkCoeff sourceCoeff transfer := by
  funext v
  refine wellFounded_lt.induction
    (C := fun v : Fin N ↦
      w v = _root_.GD.N0230.N0623.d000210 G sinkCoeff sourceCoeff transfer v) v ?_
  intro v ih
  rw [hw v, _root_.GD.N0230.N0623.d000211]
  congr 2
  apply Finset.sum_congr rfl
  intro e _he
  split_ifs with hedge
  · rw [ih (G.src e) (by simpa [hedge] using G.forward e)]
  · rfl


theorem d000214
    (G : _root_.GD.N0230.N0623.d000209 N E)
    (sinkCoeff sourceCoeff : Fin N → ℝ)
    (transfer : E → ℝ)
    (hsink : ∀ v, 0 < sinkCoeff v)
    (hsource : ∀ v, 0 < sourceCoeff v)
    (htransfer : ∀ e, 0 < transfer e) :
    ∃! w : Fin N → ℝ,
      (∀ v, 0 < w v) ∧
      ∀ v, w v =
        (sourceCoeff v + ∑ e, if G.dst e = v then
          transfer e * w (G.src e) else 0) / sinkCoeff v := by
  refine ⟨_root_.GD.N0230.N0623.d000210 G sinkCoeff sourceCoeff transfer,
    ⟨_root_.GD.N0230.N0623.d000212 G sinkCoeff sourceCoeff transfer
      hsink hsource htransfer,
      _root_.GD.N0230.N0623.d000211 G sinkCoeff sourceCoeff transfer⟩, ?_⟩
  intro w hw
  exact _root_.GD.N0230.N0623.d000213
    G sinkCoeff sourceCoeff transfer w hw.2

end RankedRecursion

section BooleanFaceCocycle

variable {A : Type*} [DecidableEq A]


def d000215
    (ratio : Finset A → A → ℝ) : Finset A → List A → ℝ
  | _, [] => 1
  | face, i :: path =>
      ratio face i * d000215 ratio (face.erase i) path


def d000216 (ratio : Finset A → A → ℝ) : Prop :=
  ∀ face i j, i ∈ face → j ∈ face → i ≠ j →
    ratio face i * ratio (face.erase i) j =
      ratio face j * ratio (face.erase j) i


theorem d000217
    (face : Finset A) (i j : A) :
    (face.erase i).erase j = (face.erase j).erase i := by
  ext x
  simp only [Finset.mem_erase]
  aesop



theorem d000218
    (ratio : Finset A → A → ℝ) (hflat : _root_.GD.N0230.N0623.d000216 ratio)
    (face : Finset A) (i j : A) (tail : List A)
    (hi : i ∈ face) (hj : j ∈ face) (hne : i ≠ j) :
    _root_.GD.N0230.N0623.d000215 ratio face (i :: j :: tail) =
      _root_.GD.N0230.N0623.d000215 ratio face (j :: i :: tail) := by
  simp only [_root_.GD.N0230.N0623.d000215]
  rw [_root_.GD.N0230.N0623.d000217, ← mul_assoc, ← mul_assoc,
    hflat face i j hi hj hne]



theorem d000219
    (ratio : Finset A → A → ℝ) :
    _root_.GD.N0230.N0623.d000216 ratio ↔
      ∀ face i j, i ∈ face → j ∈ face → i ≠ j →
        _root_.GD.N0230.N0623.d000215 ratio face [i, j] =
          _root_.GD.N0230.N0623.d000215 ratio face [j, i] := by
  constructor
  · intro hflat face i j hi hj hne
    exact _root_.GD.N0230.N0623.d000218
      ratio hflat face i j [] hi hj hne
  · intro hpaths face i j hi hj hne
    have h := hpaths face i j hi hj hne
    simpa [_root_.GD.N0230.N0623.d000215, mul_assoc] using h



def d000220
    (ratio : Finset A → A → ℝ)
    (weight : Finset A → ℝ) : Prop :=
  ∀ face i, i ∈ face →
    weight (face.erase i) = ratio face i * weight face




theorem d000221
    (ratio : Finset A → A → ℝ)
    (weight : Finset A → ℝ)
    (hweight : ∀ face, 0 < weight face)
    (hcompatible : _root_.GD.N0230.N0623.d000220 ratio weight) :
    _root_.GD.N0230.N0623.d000216 ratio := by
  intro face i j hi hj hne
  have hj' : j ∈ face.erase i :=
    Finset.mem_erase.mpr ⟨hne.symm, hj⟩
  have hi' : i ∈ face.erase j :=
    Finset.mem_erase.mpr ⟨hne, hi⟩
  have hleft := hcompatible (face.erase i) j hj'
  have hright := hcompatible (face.erase j) i hi'
  rw [hcompatible face i hi] at hleft
  rw [hcompatible face j hj] at hright
  have heq :
      (ratio face i * ratio (face.erase i) j) * weight face =
        (ratio face j * ratio (face.erase j) i) * weight face := by
    calc
      (ratio face i * ratio (face.erase i) j) * weight face =
          ratio (face.erase i) j * (ratio face i * weight face) := by ring
      _ = weight ((face.erase i).erase j) := hleft.symm
      _ = weight ((face.erase j).erase i) :=
        congrArg weight (_root_.GD.N0230.N0623.d000217 face i j)
      _ = ratio (face.erase j) i * (ratio face j * weight face) := hright
      _ = (ratio face j * ratio (face.erase j) i) * weight face := by ring
  exact mul_right_cancel₀ (hweight face).ne' heq




def d000222 (face : Finset A) (path : List A) : Prop :=
  path.Nodup ∧ ∀ i ∈ path, i ∈ face



theorem d000223
    (ratio : Finset A → A → ℝ)
    (hratio : ∀ face i, i ∈ face → 0 < ratio face i) :
    ∀ face path, _root_.GD.N0230.N0623.d000222 face path →
      0 < _root_.GD.N0230.N0623.d000215 ratio face path := by
  intro face path
  induction path generalizing face with
  | nil => simp [_root_.GD.N0230.N0623.d000215]
  | cons i tail ih =>
      intro hvalid
      have hiFace : i ∈ face := hvalid.2 i (by simp)
      have htail : _root_.GD.N0230.N0623.d000222 (face.erase i) tail := by
        constructor
        · exact hvalid.1.tail
        · intro j hj
          have hjFace : j ∈ face := hvalid.2 j (by simp [hj])
          have hji : j ≠ i := by
            intro hji
            subst j
            exact hvalid.1.notMem hj
          exact Finset.mem_erase.mpr ⟨hji, hjFace⟩
      rw [_root_.GD.N0230.N0623.d000215]
      exact mul_pos (hratio face i hiFace)
        (ih (face.erase i) htail)

section CanonicalSortedPath

variable [Fintype A] [LinearOrder A]




def d000224
    (ratio : Finset A → A → ℝ) (rootWeight : ℝ)
    (face : Finset A) : ℝ :=
  rootWeight * _root_.GD.N0230.N0623.d000215 ratio Finset.univ
    ((Finset.univ \ face).sort (· ≤ ·))


theorem d000225
    (ratio : Finset A → A → ℝ) (rootWeight : ℝ)
    (hroot : 0 < rootWeight)
    (hratio : ∀ face i, i ∈ face → 0 < ratio face i)
    (face : Finset A) :
    0 < _root_.GD.N0230.N0623.d000224 ratio rootWeight face := by
  apply mul_pos hroot
  apply _root_.GD.N0230.N0623.d000223 ratio hratio
  constructor
  · exact Finset.sort_nodup _ _
  · intro i _hi
    exact Finset.mem_univ i

end CanonicalSortedPath

end BooleanFaceCocycle

end

end N0623
end N0230
end GD

#print axioms _root_.GD.N0230.N0623.d000207
#print axioms _root_.GD.N0230.N0623.d000208
#print axioms _root_.GD.N0230.N0623.d000214
#print axioms _root_.GD.N0230.N0623.d000218
#print axioms _root_.GD.N0230.N0623.d000219
#print axioms _root_.GD.N0230.N0623.d000221
#print axioms _root_.GD.N0230.N0623.d000225
