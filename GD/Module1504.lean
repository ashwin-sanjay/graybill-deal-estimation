import GD.Module1489
import GD.Module1475
import GD.Module1483
import GD.Module1503







set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0101.N0400
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0230.N0665
open _root_.GD.N0072 _root_.GD.N0101.N0357 _root_.GD.N0101.N0399 _root_.GD.N0101.N0398
open _root_.GD.N0101.N0351
open _root_.GD.N0225.N0539
open _root_.GD.N0225.N0538

variable {n : ℕ}

local instance d023488 : MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 (n + 1)) :=
  borel (_root_.GD.N0232.N0719.N0859.d010809 (n + 1))
local instance d023489 : BorelSpace (_root_.GD.N0232.N0719.N0859.d010809 (n + 1)) := ⟨rfl⟩

theorem d023490
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < _root_.GD.N0232.N0719.N0954.d009355 sizes i + _root_.GD.N0232.N0719.N0954.d009355 sizes j)
    (p w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hpnn : ∀ t i, 0 ≤ p t i) (hwnn : ∀ t i, 0 ≤ w t i)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t)
    {L : ℝ} (hL : 0 < L)
    (hbase : Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal)
      (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L))
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes p)) :
    (∫ β, (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal - (_root_.GD.N0101.N0398.d023335 sizes hn w β).toReal
      ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L) ≤
      ∫ t in _root_.GD.N0101.N0357.d023158,
        _root_.GD.N0101.N0412.d023279
          (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L t := by
  have hpf := _root_.GD.N0225.N0538.d023463 sizes hn p hp hpunit hpnn
  obtain ⟨_, hpi, heq⟩ := _root_.GD.N0101.N0398.d023340
    sizes hn ρ L hρ p w hp hw hpunit hwunit hpf.2 hbase hweak
  rw [heq, _root_.GD.N0101.N0351.d023207 _ ρ (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ]
  apply integral_mono_ae
    ((_root_.GD.N0101.N0351.d023208 _ ρ (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ _).mp hpi)
    (_root_.GD.N0101.N0412.d023285
      _ ρ (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ hα hsum hab hL)
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  have hwIcc (i : Fin (n + 1)) : w t i ∈ Icc (0 : ℝ) 1 := by
    refine ⟨hwnn t i, ?_⟩
    calc
      w t i ≤ ∑ j, w t j := Finset.single_le_sum (fun j _ => hwnn t j) (Finset.mem_univ i)
      _ = 1 := hwunit t
  change _root_.GD.N0101.N0357.d023162 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ t *
      (_root_.GD.N0101.N0412.d023276 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L (p t) t -
        _root_.GD.N0101.N0412.d023276 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L (w t) t) ≤ _
  rw [hporacle t ht]
  exact (le_max_right 0 _).trans
    (_root_.GD.N0101.N0412.d023284
      _ t (w t) (_root_.GD.N0232.N0719.N0954.d009358 hn) ht hρ hL hwIcc (hwunit t))




theorem d023491
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < _root_.GD.N0232.N0719.N0954.d009355 sizes i + _root_.GD.N0232.N0719.N0954.d009355 sizes j)
    (p : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hp : Measurable p) (hpunit : ∀ t, ∑ i, p t i = 1) (hpnn : ∀ t i, 0 ≤ p t i)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t)
    (hbaseInt : ∀ m : ℕ, Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal)
      (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) ((m : ℝ) + 1))) :
    ¬ ∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes p) := by
  apply _root_.GD.N0225.N0540.d023486
      sizes hn (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
      (_root_.GD.N0101.N0399.d023328 sizes (fun i => by have := hn i; omega))
      (_root_.GD.N0101.N0399.d023329 sizes _) p hp hpunit hpnn hbaseInt
      (fun m : ℕ => ∫ t in _root_.GD.N0101.N0357.d023158,
        _root_.GD.N0101.N0412.d023279
          (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ ((m : ℝ) + 1) t)
      (_root_.GD.N0101.N0412.d023287
        _ ρ (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ hα hsum hab)
  intro w hw hwunit hwnn hweak m
  exact _root_.GD.N0101.N0400.d023490 sizes hn ρ hρ hα hsum hab
    p w hp hw hpunit hwunit hpnn hwnn hporacle (by positivity) (hbaseInt m) hweak

end
end GD.N0101.N0400

#print axioms _root_.GD.N0101.N0400.d023490
#print axioms _root_.GD.N0101.N0400.d023491
