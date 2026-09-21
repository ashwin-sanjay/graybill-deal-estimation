import GD.Module1609
import GD.Module1566
import GD.Module1574
import GD.Module1573






















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1709
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1726
open _root_.GD.N0106.N0428.N0770.N1715
open _root_.GD.N0106.N0428.N0770.N1711




def d027470 (q : ℝ) (p : ℝ × ℝ) : ℝ := 2 * (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024130 p + _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024130 p ^ 2


def d027471 (q : ℝ) : ℝ := (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027470 q p ∂(volume.prod volume)


def d027472 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : (ℝ × ℝ) → ℝ := _root_.GD.N0106.N0428.N0770.N1725.d024125 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 _root_.GD.N0106.N0428.N0770.N1725.d024116

theorem d027473 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024130 p = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, _root_.GD.N0106.N0428.N0770.N1728.d024390 i * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p :=
  _root_.GD.N0106.N0428.N0770.N1728.d024393 p




def d027474 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : Fin 12 :=
  ⟨2 * i.1.val + i.2.val, by have := i.1.isLt; have := i.2.isLt; omega⟩

theorem d027475 : Function.Injective _root_.GD.N0106.N0428.N0770.N1709.d027474 := by
  intro i j h
  have h' : 2 * i.1.val + i.2.val = 2 * j.1.val + j.2.val := congrArg Fin.val h
  have hi := i.2.isLt
  have hj := j.2.isLt
  have h1 : i.1.val = j.1.val := by omega
  have h2 : i.2.val = j.2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem d027476 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : _root_.GD.N0106.N0428.N0770.N1726.d024364 (_root_.GD.N0106.N0428.N0770.N1709.d027474 i) = _root_.GD.N0106.N0428.N0770.N1709.d027472 i := by
  rcases i with ⟨r, s⟩
  fin_cases r <;> fin_cases s <;>
    (funext p
     first
     | norm_num [_root_.GD.N0106.N0428.N0770.N1726.d024364, _root_.GD.N0106.N0428.N0770.N1709.d027472, _root_.GD.N0106.N0428.N0770.N1709.d027474, _root_.GD.N0106.N0428.N0770.N1726.d024361, _root_.GD.N0106.N0428.N0770.N1726.d024360, _root_.GD.N0106.N0428.N0770.N1726.d024362, _root_.GD.N0106.N0428.N0770.N1726.d024363, _root_.GD.N0106.N0428.N0770.N1728.d024389,
         _root_.GD.N0106.N0428.N0770.N1728.d024388, _root_.GD.N0106.N0428.N0770.N1725.d024127, _root_.GD.N0106.N0428.N0770.N1725.d024128]
     | (simp [_root_.GD.N0106.N0428.N0770.N1726.d024364, _root_.GD.N0106.N0428.N0770.N1709.d027472, _root_.GD.N0106.N0428.N0770.N1709.d027474, _root_.GD.N0106.N0428.N0770.N1726.d024361, _root_.GD.N0106.N0428.N0770.N1726.d024360, _root_.GD.N0106.N0428.N0770.N1726.d024362, _root_.GD.N0106.N0428.N0770.N1726.d024363, _root_.GD.N0106.N0428.N0770.N1728.d024389,
          _root_.GD.N0106.N0428.N0770.N1728.d024388, _root_.GD.N0106.N0428.N0770.N1725.d024127, _root_.GD.N0106.N0428.N0770.N1725.d024128]
        norm_num))

theorem d027477 {i j : _root_.GD.N0106.N0428.N0770.N1728.d024386} (hij : i ≠ j) (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1709.d027472 i p * _root_.GD.N0106.N0428.N0770.N1709.d027472 j p = 0 := by
  rw [← _root_.GD.N0106.N0428.N0770.N1709.d027476, ← _root_.GD.N0106.N0428.N0770.N1709.d027476]
  exact _root_.GD.N0106.N0428.N0770.N1726.d024381 _ _ (fun h => hij (_root_.GD.N0106.N0428.N0770.N1709.d027475 h)) p

theorem d027478 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024130 p ^ 2 = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 := by
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027473, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [mul_mul_mul_comm, _root_.GD.N0106.N0428.N0770.N1709.d027477 (Ne.symm hji), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h



theorem d027479 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) {p : ℝ × ℝ} (hp : p ∉ _root_.GD.N0106.N0428.N0770.N1726.d024366) : _root_.GD.N0106.N0428.N0770.N1709.d027472 i p = 0 := by
  rw [← _root_.GD.N0106.N0428.N0770.N1709.d027476]
  by_contra h
  exact hp (_root_.GD.N0106.N0428.N0770.N1726.d024380 (_root_.GD.N0106.N0428.N0770.N1709.d027474 i) (subset_tsupport _ h))

theorem d027480 {p : ℝ × ℝ} (hp : p ∉ _root_.GD.N0106.N0428.N0770.N1726.d024366) : _root_.GD.N0106.N0428.N0770.N1725.d024130 p = 0 := by
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027473]
  exact Finset.sum_eq_zero (fun i _ => by rw [_root_.GD.N0106.N0428.N0770.N1709.d027479 i hp, mul_zero])

theorem d027481 (q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1709.d027471 q = (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027470 q p ∂(volume.prod volume) := by
  unfold _root_.GD.N0106.N0428.N0770.N1709.d027471
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  simp [_root_.GD.N0106.N0428.N0770.N1709.d027470, _root_.GD.N0106.N0428.N0770.N1709.d027480 hp]



theorem d027482 (q : ℝ) : Continuous (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024169 q p.1 p.2) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
  fun_prop

theorem d027483 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {s : Set (ℝ × ℝ)}
    (hs : ∀ p ∈ s, 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2) : ContinuousOn (_root_.GD.N0106.N0428.N0770.N1725.d024170 q) s := by
  have hN : ∀ p ∈ s, 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q p.1 p.2 := fun p hp =>
    _root_.GD.N0106.N0428.N0770.N1725.d024172 hq ⟨(hs p hp).1, (hs p hp).2.1⟩ (hs p hp).2.2
  have hlog : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1711.d024178 q p.1 p.2) s := by
    unfold _root_.GD.N0106.N0428.N0770.N1711.d024178
    refine ContinuousOn.sub (ContinuousOn.mul continuousOn_const ?_)
      (ContinuousOn.mul continuousOn_const ?_)
    · refine ContinuousOn.sub (ContinuousOn.sub ?_ ?_) ?_
      · exact continuousOn_snd.log (fun p hp => (hs p hp).2.2.ne')
      · exact continuousOn_fst.log (fun p hp => (hs p hp).1.ne')
      · exact (continuousOn_const.sub continuousOn_fst).log
          (fun p hp => (sub_pos.mpr (hs p hp).2.1).ne')
    · exact (_root_.GD.N0106.N0428.N0770.N1709.d027482 q).continuousOn.log (fun p hp => (hN p hp).ne')
  have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (_root_.GD.N0106.N0428.N0770.N1711.d024178 q p.1 p.2)) s :=
    Real.continuous_exp.comp_continuousOn hlog
  refine hexp.congr (fun p hp => ?_)
  have h := hs p hp
  exact _root_.GD.N0106.N0428.N0770.N1711.d024179 h.1 h.2.1 h.2.2 (hN p hp)



def d027484 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℝ := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - _root_.GD.N0106.N0428.N0770.N1725.d024116
def d027485 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℝ := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 + _root_.GD.N0106.N0428.N0770.N1725.d024116
def d027486 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℝ := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 - _root_.GD.N0106.N0428.N0770.N1725.d024116
def d027487 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℝ := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 + _root_.GD.N0106.N0428.N0770.N1725.d024116


def d027488 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : Set (ℝ × ℝ) := Icc (_root_.GD.N0106.N0428.N0770.N1709.d027484 i) (_root_.GD.N0106.N0428.N0770.N1709.d027485 i) ×ˢ Icc (_root_.GD.N0106.N0428.N0770.N1709.d027486 i) (_root_.GD.N0106.N0428.N0770.N1709.d027487 i)

theorem d027489 {i : _root_.GD.N0106.N0428.N0770.N1728.d024386} (helo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i) (hehi : _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1) (hflo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i)
    {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0770.N1709.d027488 i) : 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, _⟩⟩ := hp
  exact ⟨helo.trans_le h1, h2.trans_lt hehi, hflo.trans_le h3⟩

theorem d027490 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {i : _root_.GD.N0106.N0428.N0770.N1728.d024386}
    (helo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i) (hehi : _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1) (hflo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i) :
    ContinuousOn (_root_.GD.N0106.N0428.N0770.N1725.d024170 q) (_root_.GD.N0106.N0428.N0770.N1709.d027488 i) :=
  _root_.GD.N0106.N0428.N0770.N1709.d027483 hq (fun p hp => _root_.GD.N0106.N0428.N0770.N1709.d027489 helo hehi hflo hp)

theorem d027491 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {i : _root_.GD.N0106.N0428.N0770.N1728.d024386}
    (helo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i) (hehi : _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1) (hflo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i) :
    Integrable (fun p => (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p) (volume.prod volume) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p) (_root_.GD.N0106.N0428.N0770.N1709.d027488 i) :=
    (continuousOn_fst.sub continuousOn_const).mul (_root_.GD.N0106.N0428.N0770.N1709.d027490 hq helo hehi hflo)
  have h := _root_.GD.N0106.N0428.N0770.N1715.d027466 (c := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1) (f := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2)
    (w := _root_.GD.N0106.N0428.N0770.N1725.d024116) hcont (_root_.GD.N0106.N0428.N0770.N1725.d024133 _ _) (_root_.GD.N0106.N0428.N0770.N1725.d024133 _ _)
    (fun x hx => _root_.GD.N0106.N0428.N0770.N1715.d027456 _root_.GD.N0106.N0428.N0770.N1725.d024120 hx) (fun y hy => _root_.GD.N0106.N0428.N0770.N1715.d027456 _root_.GD.N0106.N0428.N0770.N1725.d024120 hy)
  exact h

theorem d027492 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {i : _root_.GD.N0106.N0428.N0770.N1728.d024386}
    (helo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i) (hehi : _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1) (hflo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2) (volume.prod volume) := by
  have hcont : ContinuousOn (_root_.GD.N0106.N0428.N0770.N1725.d024170 q) (_root_.GD.N0106.N0428.N0770.N1709.d027488 i) := _root_.GD.N0106.N0428.N0770.N1709.d027490 hq helo hehi hflo
  have h := _root_.GD.N0106.N0428.N0770.N1715.d027466 (c := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1) (f := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2)
    (w := _root_.GD.N0106.N0428.N0770.N1725.d024116) (ρe := fun x => _root_.GD.N0106.N0428.N0770.N1725.d024124 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 _root_.GD.N0106.N0428.N0770.N1725.d024116 x ^ 2)
    (ρF := fun y => _root_.GD.N0106.N0428.N0770.N1725.d024124 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 _root_.GD.N0106.N0428.N0770.N1725.d024116 y ^ 2) hcont
    ((_root_.GD.N0106.N0428.N0770.N1725.d024133 _ _).pow 2) ((_root_.GD.N0106.N0428.N0770.N1725.d024133 _ _).pow 2)
    (fun x hx => by
      show _root_.GD.N0106.N0428.N0770.N1725.d024124 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 _root_.GD.N0106.N0428.N0770.N1725.d024116 x ^ 2 = 0
      rw [_root_.GD.N0106.N0428.N0770.N1715.d027456 _root_.GD.N0106.N0428.N0770.N1725.d024120 hx]
      simp)
    (fun y hy => by
      show _root_.GD.N0106.N0428.N0770.N1725.d024124 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 _root_.GD.N0106.N0428.N0770.N1725.d024116 y ^ 2 = 0
      rw [_root_.GD.N0106.N0428.N0770.N1715.d027456 _root_.GD.N0106.N0428.N0770.N1725.d024120 hy]
      simp)
  have heq : (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2) =
      fun p => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * (_root_.GD.N0106.N0428.N0770.N1725.d024124 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 _root_.GD.N0106.N0428.N0770.N1725.d024116 p.1 ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024124 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 _root_.GD.N0106.N0428.N0770.N1725.d024116 p.2 ^ 2) := by
    funext p
    simp only [_root_.GD.N0106.N0428.N0770.N1709.d027472, _root_.GD.N0106.N0428.N0770.N1725.d024125]
    ring
  rw [heq]
  exact h



theorem d027493 (q : ℝ) :
    (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027470 q p) =
      fun p => ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p) +
        _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2)) := by
  funext p
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027470, _root_.GD.N0106.N0428.N0770.N1709.d027478, _root_.GD.N0106.N0428.N0770.N1709.d027473, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem d027494 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i ∧ _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i) :
    ∀ i ∈ (Finset.univ : Finset _root_.GD.N0106.N0428.N0770.N1728.d024386),
      Integrable (fun p : ℝ × ℝ => 2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p) +
        _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2)) (volume.prod volume) :=
  fun i _ => ((_root_.GD.N0106.N0428.N0770.N1709.d027491 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _).add
    ((_root_.GD.N0106.N0428.N0770.N1709.d027492 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _)

theorem d027495 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i ∧ _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i) :
    Integrable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027470 q p) (volume.prod volume) := by
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027493]
  exact integrable_finsetSum _ (_root_.GD.N0106.N0428.N0770.N1709.d027494 hq hgeom)

theorem d027496 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i ∧ _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027470 q p ∂(volume.prod volume)) =
      ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i *
          (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) +
        _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 *
          (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume))) := by
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027493, integral_finsetSum _ (_root_.GD.N0106.N0428.N0770.N1709.d027494 hq hgeom)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_add ((_root_.GD.N0106.N0428.N0770.N1709.d027491 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _)
    ((_root_.GD.N0106.N0428.N0770.N1709.d027492 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _),
    integral_const_mul, integral_const_mul]




def d027497 (k A1 A2 D : ℝ) : ℝ := 2 * (k * A1) + D * (k * (A1 ^ 2 + A2))

def d027498 (k B1 B2 D : ℝ) : ℝ := D * (k * (B1 ^ 2 + B2))

def d027499 (k A1 A2 : ℝ) : ℝ := k * (A1 ^ 2 + A2)

def d027500 (k B1 B2 : ℝ) : ℝ := k * (B1 ^ 2 + B2)



theorem d027501 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386)
    {eprod pmin k A1 A2 B1 B2 D : ℝ}
    (helo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i) (hehi : _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1) (hflo : 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ _root_.GD.N0106.N0428.N0770.N1709.d027484 i) (hpmin2 : pmin ≤ 1 / 2 + _root_.GD.N0106.N0428.N0770.N1709.d027486 i / 4)
    (heprod : 0 < eprod) (hE1 : eprod ≤ _root_.GD.N0106.N0428.N0770.N1709.d027484 i * (1 - _root_.GD.N0106.N0428.N0770.N1709.d027484 i)) (hE2 : eprod ≤ _root_.GD.N0106.N0428.N0770.N1709.d027485 i * (1 - _root_.GD.N0106.N0428.N0770.N1709.d027485 i))
    (hk : 0 ≤ k) (hkk : _root_.GD.N0106.N0428.N0770.N1709.d027487 i ≤ k ^ 2 * (eprod * pmin ^ 5))
    (hA1 : (1 / 2) * (1 / _root_.GD.N0106.N0428.N0770.N1709.d027484 i + 1 / (1 - _root_.GD.N0106.N0428.N0770.N1709.d027485 i)) + (5 / 2) * (1 / pmin) ≤ A1)
    (hA2 : (1 / 2) * (1 / _root_.GD.N0106.N0428.N0770.N1709.d027484 i ^ 2 + 1 / (1 - _root_.GD.N0106.N0428.N0770.N1709.d027485 i) ^ 2) + (5 / 2) * (1 / pmin ^ 2) ≤ A2)
    (hB1 : (1 / 2) * (1 / _root_.GD.N0106.N0428.N0770.N1709.d027486 i) + (5 / 8) * (1 / pmin) ≤ B1)
    (hB2 : (1 / 2) * (1 / _root_.GD.N0106.N0428.N0770.N1709.d027486 i ^ 2) + (5 / 32) * (1 / pmin ^ 2) ≤ B2)
    (hD1 : _root_.GD.N0106.N0428.N0770.N1709.d027485 i ≤ D) (hD2 : 1 / 2 - _root_.GD.N0106.N0428.N0770.N1709.d027484 i ≤ D) :
    |(_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) -
        ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)| ≤
      (_root_.GD.N0106.N0428.N0770.N1709.d027497 k A1 A2 D + _root_.GD.N0106.N0428.N0770.N1709.d027498 k B1 B2 D) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 / 12 ∧
    |(_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) -
        (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)| ≤
      (_root_.GD.N0106.N0428.N0770.N1709.d027499 k A1 A2 + _root_.GD.N0106.N0428.N0770.N1709.d027500 k B1 B2) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 / 45 := by
  have hq0 : 0 ≤ q := hq.1
  have hq12 : q ≤ 1 / 2 := hq.2
  have hq1 : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans (by norm_num)⟩
  have hehi' : _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1 := hehi
  have heta2 : _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 ≠ 0 := pow_ne_zero 2 _root_.GD.N0106.N0428.N0770.N1725.d024120.ne'
  set c := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 with hc
  set f := (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 with hf
  have hc_lo : _root_.GD.N0106.N0428.N0770.N1709.d027484 i = c - _root_.GD.N0106.N0428.N0770.N1725.d024116 := rfl
  have hc_hi : _root_.GD.N0106.N0428.N0770.N1709.d027485 i = c + _root_.GD.N0106.N0428.N0770.N1725.d024116 := rfl
  have hf_lo : _root_.GD.N0106.N0428.N0770.N1709.d027486 i = f - _root_.GD.N0106.N0428.N0770.N1725.d024116 := rfl
  have hf_hi : _root_.GD.N0106.N0428.N0770.N1709.d027487 i = f + _root_.GD.N0106.N0428.N0770.N1725.d024116 := rfl

  have hreg : ∀ e ∈ Icc (c - _root_.GD.N0106.N0428.N0770.N1725.d024116) (c + _root_.GD.N0106.N0428.N0770.N1725.d024116), ∀ F ∈ Icc (f - _root_.GD.N0106.N0428.N0770.N1725.d024116) (f + _root_.GD.N0106.N0428.N0770.N1725.d024116),
      0 < e ∧ e < 1 ∧ 0 < F ∧ pmin ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ∧ 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
    intro e he F hF
    have he0 : 0 < e := by rw [hc_lo] at helo; linarith [he.1]
    have he1 : e < 1 := by rw [hc_hi] at hehi'; linarith [he.2]
    have hF0 : 0 < F := by rw [hf_lo] at hflo; linarith [hF.1]
    have hNp : pmin ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
      refine (le_min hpmin1 hpmin2).trans ?_
      rw [hc_lo, hf_lo]
      exact _root_.GD.N0106.N0428.N0770.N1711.d024207 hq0 hq12 he.1 (by rw [hf_lo] at hflo; exact hflo.le) hF.1
    exact ⟨he0, he1, hF0, hNp, hpmin0.trans_le hNp⟩
  have hf_mem : f ∈ Icc (f - _root_.GD.N0106.N0428.N0770.N1725.d024116) (f + _root_.GD.N0106.N0428.N0770.N1725.d024116) := ⟨by linarith [_root_.GD.N0106.N0428.N0770.N1725.d024120], by linarith [_root_.GD.N0106.N0428.N0770.N1725.d024120]⟩

  have hWk : ∀ e ∈ Icc (c - _root_.GD.N0106.N0428.N0770.N1725.d024116) (c + _root_.GD.N0106.N0428.N0770.N1725.d024116), ∀ F ∈ Icc (f - _root_.GD.N0106.N0428.N0770.N1725.d024116) (f + _root_.GD.N0106.N0428.N0770.N1725.d024116),
      0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) ∧ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) ≤ k := by
    intro e he F hF
    obtain ⟨he0, he1, hF0, hNp, hN⟩ := hreg e he F hF
    refine ⟨(_root_.GD.N0106.N0428.N0770.N1711.d024180 he0 he1 hF0 hN).le, ?_⟩
    have hE : eprod ≤ e * (1 - e) := by
      rw [hc_lo] at hE1; rw [hc_hi] at hE2
      exact _root_.GD.N0106.N0428.N0770.N1711.d024208 he.1 he.2 hE1 hE2
    have hfhi' : F ≤ f + _root_.GD.N0106.N0428.N0770.N1725.d024116 := hF.2
    rw [hf_hi] at hkk
    exact _root_.GD.N0106.N0428.N0770.N1711.d024209 hq1 he0 he1 hF0 hE heprod hfhi' hpmin0 hNp hk hkk
  have hLe : ∀ e ∈ Icc (c - _root_.GD.N0106.N0428.N0770.N1725.d024116) (c + _root_.GD.N0106.N0428.N0770.N1725.d024116), ∀ F ∈ Icc (f - _root_.GD.N0106.N0428.N0770.N1725.d024116) (f + _root_.GD.N0106.N0428.N0770.N1725.d024116),
      |_root_.GD.N0106.N0428.N0770.N1711.d024186 q e F| ≤ A1 ∧ |_root_.GD.N0106.N0428.N0770.N1711.d024187 q e F| ≤ A2 := by
    intro e he F hF
    obtain ⟨_, _, _, hNp, _⟩ := hreg e he F hF
    have helo' : 0 < c - _root_.GD.N0106.N0428.N0770.N1725.d024116 := by rw [hc_lo] at helo; exact helo
    have hehi'' : c + _root_.GD.N0106.N0428.N0770.N1725.d024116 < 1 := by rw [hc_hi] at hehi'; exact hehi'
    rw [hc_lo, hc_hi] at hA1 hA2
    exact ⟨(_root_.GD.N0106.N0428.N0770.N1711.d024210 hq0 hq12 helo' he.1 he.2 hehi'' hpmin0 hNp).trans hA1,
      (_root_.GD.N0106.N0428.N0770.N1711.d024212 hq0 hq12 helo' he.1 he.2 hehi'' hpmin0 hNp).trans hA2⟩
  have hLF : ∀ e ∈ Icc (c - _root_.GD.N0106.N0428.N0770.N1725.d024116) (c + _root_.GD.N0106.N0428.N0770.N1725.d024116), ∀ F ∈ Icc (f - _root_.GD.N0106.N0428.N0770.N1725.d024116) (f + _root_.GD.N0106.N0428.N0770.N1725.d024116),
      |_root_.GD.N0106.N0428.N0770.N1711.d024199 q e F| ≤ B1 ∧ |_root_.GD.N0106.N0428.N0770.N1711.d024200 q e F| ≤ B2 := by
    intro e he F hF
    obtain ⟨_, _, _, hNp, _⟩ := hreg e he F hF
    have hflo' : 0 < f - _root_.GD.N0106.N0428.N0770.N1725.d024116 := by rw [hf_lo] at hflo; exact hflo
    rw [hf_lo] at hB1 hB2
    exact ⟨(_root_.GD.N0106.N0428.N0770.N1711.d024213 hq0 hq12 hflo' hF.1 hpmin0 hNp).trans hB1,
      (_root_.GD.N0106.N0428.N0770.N1711.d024214 hq0 hq12 hflo' hF.1 hpmin0 hNp).trans hB2⟩
  have hDq : ∀ e ∈ Icc (c - _root_.GD.N0106.N0428.N0770.N1725.d024116) (c + _root_.GD.N0106.N0428.N0770.N1725.d024116), |e - q| ≤ D := by
    intro e he
    rw [hc_hi] at hD1; rw [hc_lo] at hD2
    exact _root_.GD.N0106.N0428.N0770.N1711.d024218 hq0 hq12 he.1 he.2 hD1 hD2
  have hcontW : ContinuousOn (_root_.GD.N0106.N0428.N0770.N1725.d024170 q) (Icc (c - _root_.GD.N0106.N0428.N0770.N1725.d024116) (c + _root_.GD.N0106.N0428.N0770.N1725.d024116) ×ˢ Icc (f - _root_.GD.N0106.N0428.N0770.N1725.d024116) (f + _root_.GD.N0106.N0428.N0770.N1725.d024116)) :=
    _root_.GD.N0106.N0428.N0770.N1709.d027490 hq1 helo hehi hflo
  have hcenter : _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c, f) = _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i) := by rw [hc, hf]
  constructor
  ·
    have h := _root_.GD.N0106.N0428.N0770.N1715.d027468 (g := fun p : ℝ × ℝ => (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p)
      (gF := fun e F => (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F))
      (gFF := fun e F => (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024200 q e F))
      (gE := fun e => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) + (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e f))
      (gEE := fun e => 2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e f) +
        (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e f * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e f + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) * _root_.GD.N0106.N0428.N0770.N1711.d024187 q e f))
      (ME := _root_.GD.N0106.N0428.N0770.N1709.d027497 k A1 A2 D) (MF := _root_.GD.N0106.N0428.N0770.N1709.d027498 k B1 B2 D) _root_.GD.N0106.N0428.N0770.N1725.d024120
      ((continuousOn_fst.sub continuousOn_const).mul hcontW)
      (fun e he F hF => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he F hF
        exact _root_.GD.N0106.N0428.N0770.N1711.d024205 he0 he1 hF0 hN)
      (fun e he F hF => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he F hF
        exact _root_.GD.N0106.N0428.N0770.N1711.d024206 he0 he1 hF0 hN)
      (fun e he F hF => by
        obtain ⟨hW0, hWk'⟩ := hWk e he F hF
        obtain ⟨hB1', hB2'⟩ := hLF e he F hF
        exact _root_.GD.N0106.N0428.N0770.N1711.d024217 hW0 hWk' hB1' hB2' (hDq e he))
      (fun e he => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he f hf_mem
        exact _root_.GD.N0106.N0428.N0770.N1711.d024192 he0 he1 hF0 hN)
      (fun e he => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he f hf_mem
        exact _root_.GD.N0106.N0428.N0770.N1711.d024193 he0 he1 hF0 hN)
      (fun e he => by
        obtain ⟨hW0, hWk'⟩ := hWk e he f hf_mem
        obtain ⟨hA1', hA2'⟩ := hLe e he f hf_mem
        exact _root_.GD.N0106.N0428.N0770.N1711.d024216 hW0 hWk' hA1' hA2' (hDq e he))

    have hpos : 0 < (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ := inv_pos.mpr (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2)
    have hI : (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) =
        ∫ p, (fun p : ℝ × ℝ => (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p) p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ∂(volume.prod volume) := by
      rfl
    rw [hI, ← hcenter]
    have hscale : (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * (∫ p, (fun p : ℝ × ℝ => (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p) p *
        _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ∂(volume.prod volume)) - (c - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c, f) =
        (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ((∫ p, (fun p : ℝ × ℝ => (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p) p *
          _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ∂(volume.prod volume)) - (c - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c, f) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2) := by
      rw [mul_sub]
      congr 1
      field_simp [_root_.GD.N0106.N0428.N0770.N1725.d024120.ne'] <;> ring
    rw [hscale, abs_mul, abs_of_pos hpos]
    calc (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * |(∫ p, (fun p : ℝ × ℝ => (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p) p *
          _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ∂(volume.prod volume)) - (c - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c, f) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2|
        ≤ (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ((_root_.GD.N0106.N0428.N0770.N1709.d027497 k A1 A2 D + _root_.GD.N0106.N0428.N0770.N1709.d027498 k B1 B2 D) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 4 / 12) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = (_root_.GD.N0106.N0428.N0770.N1709.d027497 k A1 A2 D + _root_.GD.N0106.N0428.N0770.N1709.d027498 k B1 B2 D) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 / 12 := by
          field_simp [_root_.GD.N0106.N0428.N0770.N1725.d024120.ne'] <;> ring
  ·
    have h := _root_.GD.N0106.N0428.N0770.N1715.d027469 (g := _root_.GD.N0106.N0428.N0770.N1725.d024170 q)
      (gF := fun e F => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F)
      (gFF := fun e F => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024200 q e F)
      (gE := fun e => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e f)
      (gEE := fun e => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e f * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e f + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f) * _root_.GD.N0106.N0428.N0770.N1711.d024187 q e f)
      (ME := _root_.GD.N0106.N0428.N0770.N1709.d027499 k A1 A2) (MF := _root_.GD.N0106.N0428.N0770.N1709.d027500 k B1 B2) _root_.GD.N0106.N0428.N0770.N1725.d024120 hcontW
      (fun e he F hF => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he F hF
        exact _root_.GD.N0106.N0428.N0770.N1711.d024202 he0 he1 hF0 hN)
      (fun e he F hF => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he F hF
        exact _root_.GD.N0106.N0428.N0770.N1711.d024204 he0 he1 hF0 hN)
      (fun e he F hF => by
        obtain ⟨hW0, hWk'⟩ := hWk e he F hF
        obtain ⟨hB1', hB2'⟩ := hLF e he F hF
        exact _root_.GD.N0106.N0428.N0770.N1711.d024215 hW0 hWk' hB1' hB2')
      (fun e he => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he f hf_mem
        exact _root_.GD.N0106.N0428.N0770.N1711.d024189 he0 he1 hF0 hN)
      (fun e he => by
        obtain ⟨he0, he1, hF0, _, hN⟩ := hreg e he f hf_mem
        exact _root_.GD.N0106.N0428.N0770.N1711.d024191 he0 he1 hF0 hN)
      (fun e he => by
        obtain ⟨hW0, hWk'⟩ := hWk e he f hf_mem
        obtain ⟨hA1', hA2'⟩ := hLe e he f hf_mem
        exact _root_.GD.N0106.N0428.N0770.N1711.d024215 hW0 hWk' hA1' hA2')
    have hpos : 0 < (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ := inv_pos.mpr (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2)
    have hI : (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) =
        ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ^ 2 ∂(volume.prod volume) := by
      rfl
    rw [hI, ← hcenter]
    have hscale : (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ^ 2 ∂(volume.prod volume)) -
        (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c, f) =
        (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ((∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ^ 2 ∂(volume.prod volume)) -
          _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c, f) * (4 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 / 9)) := by
      rw [mul_sub]
      congr 1
      field_simp [_root_.GD.N0106.N0428.N0770.N1725.d024120.ne'] <;> ring
    rw [hscale, abs_mul, abs_of_pos hpos]
    calc (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * |(∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024116 p ^ 2 ∂(volume.prod volume)) -
          _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c, f) * (4 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 / 9)|
        ≤ (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ((_root_.GD.N0106.N0428.N0770.N1709.d027499 k A1 A2 + _root_.GD.N0106.N0428.N0770.N1709.d027500 k B1 B2) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 4 / 45) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = (_root_.GD.N0106.N0428.N0770.N1709.d027499 k A1 A2 + _root_.GD.N0106.N0428.N0770.N1709.d027500 k B1 B2) * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 / 45 := by
          field_simp [_root_.GD.N0106.N0428.N0770.N1725.d024120.ne'] <;> ring



theorem d027502 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i ∧ _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i) :
    _root_.GD.N0106.N0428.N0770.N1709.d027471 q - _root_.GD.N0106.N0428.N0770.N1728.d024397 q = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) -
          ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)) +
        _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) - (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))) := by
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027481, _root_.GD.N0106.N0428.N0770.N1709.d027496 hq hgeom, _root_.GD.N0106.N0428.N0770.N1728.d024397, _root_.GD.N0106.N0428.N0770.N1728.d024407, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem d027503 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1709.d027484 i ∧ _root_.GD.N0106.N0428.N0770.N1709.d027485 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1709.d027486 i)
    {err1 err2 : _root_.GD.N0106.N0428.N0770.N1728.d024386 → ℝ}
    (h1 : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, |(_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
        (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) -
        ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)| ≤ err1 i)
    (h2 : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, |(_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) - (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)| ≤ err2 i) :
    |_root_.GD.N0106.N0428.N0770.N1709.d027471 q - _root_.GD.N0106.N0428.N0770.N1728.d024397 q| ≤ ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * |_root_.GD.N0106.N0428.N0770.N1728.d024390 i| * err1 i + _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * err2 i) := by
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027502 hq hgeom]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have ha : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 := mul_nonneg _root_.GD.N0106.N0428.N0770.N1725.d024122.le (sq_nonneg _)
  calc |2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) -
          ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)) +
        _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) - (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))|
      ≤ |2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) -
          ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))| +
        |_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) - (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))| := by
        first
        | exact abs_add_le _ _
        | exact abs_add _ _
    _ ≤ 2 * |_root_.GD.N0106.N0428.N0770.N1728.d024390 i| * err1 i + _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * err2 i := by
        rw [abs_mul (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i), abs_mul (2 : ℝ) (_root_.GD.N0106.N0428.N0770.N1728.d024390 i),
          abs_mul (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2), abs_two, abs_of_nonneg ha]
        exact add_le_add (mul_le_mul_of_nonneg_left (h1 i) (by positivity))
          (mul_le_mul_of_nonneg_left (h2 i) ha)

end
end GD.N0106.N0428.N0770.N1709

#print axioms _root_.GD.N0106.N0428.N0770.N1709.d027478
#print axioms _root_.GD.N0106.N0428.N0770.N1709.d027481
#print axioms _root_.GD.N0106.N0428.N0770.N1709.d027496
#print axioms _root_.GD.N0106.N0428.N0770.N1709.d027501
#print axioms _root_.GD.N0106.N0428.N0770.N1709.d027503
