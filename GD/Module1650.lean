import GD.Module1419

import GD.Module0783
import GD.Module0747

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators Classical

namespace GD.N0027.N0284

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0896 _root_.GD.N0232.N0719.N0843
open _root_.GD.N0232.N0719.N0815 _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0812 _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0810
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0823 _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0941 _root_.GD.N0232.N0719.N0974
open _root_.GD.N0232.N0719.N0946

variable (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)

def d028086 (S : Set (_root_.GD.N0232.N0719.N0859.d010809 k))
    (hS : ∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ theta,
      _root_.GD.N0232.N0719.N0896.d011104 k g theta ∈ S ↔ theta ∈ S)
    (C : ℝ) (hC : 0 < C) : _root_.GD.N0232.N0719.N0843.d012215 k where
  value theta := (if theta ∈ S then C else 1) * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta
  positive theta := mul_pos (by split_ifs <;> positivity)
    (_root_.GD.N0232.N0719.N0972.d012342 k sizes hk hn theta)
  character g theta := by
    rw [show _root_.GD.N0232.N0719.N0972.d012340 k sizes (_root_.GD.N0232.N0719.N0896.d011104 k g theta) =
      g.d009239 ^ 2 * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta from
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn).character g theta]
    simp only [hS g theta]
    ring

include hk hn in
theorem d028087
    (S : Set (_root_.GD.N0232.N0719.N0859.d010809 k))
    (hS : ∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ theta,
      _root_.GD.N0232.N0719.N0896.d011104 k g theta ∈ S ↔ theta ∈ S)
    (C : ℝ) (hC : 0 < C)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (hglobal : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes theta))
    (hlocal : ∀ theta ∈ S, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta)) :
    ∀ theta ∈ S, _root_.GD.N0232.N0719.N0941.d020687 k sizes theta ≤ C := by
  classical
  let gamma := _root_.GD.N0027.N0284.d028086 k sizes hk hn S hS C hC
  have hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (1 * gamma.value theta) := by
    intro theta
    by_cases ht : theta ∈ S
    · simpa [gamma, _root_.GD.N0027.N0284.d028086, ht] using hlocal theta ht
    · simpa [gamma, _root_.GD.N0027.N0284.d028086, ht] using hglobal theta
  obtain ⟨e, hem, heq, heb⟩ := _root_.GD.N0232.N0719.N0843.d012245
    k sizes gamma hk hn 1 (by norm_num) f hf hb
  have he : ∀ b : ℝ, ∀ x, e (fun i j => b + x i j) = b + e x := by
    intro b x
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, 0⟩
    have h := heq g x
    have h' : e (_root_.GD.N0232.N0719.N0900.d009095 k sizes b 1 x) = b + e x := by
      simpa [g, _root_.GD.N0232.N0719.N0946.d009258,
        _root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0719.N0946.d009229.d009239, _root_.GD.N0232.N0719.N0946.d009229.shift] using h
    have hfun : _root_.GD.N0232.N0719.N0900.d009095 k sizes b 1 x =
        (fun i j => b + x i j) := by
      funext i j
      change b + 1 * x i j = b + x i j
      ring
    rw [hfun] at h'
    exact h'
  intro theta ht
  have hbound : _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta) := by
    simpa [gamma, _root_.GD.N0027.N0284.d028086, ht] using heb theta
  have hr := _root_.GD.N0232.N0719.N0974.d019823 sizes theta e hem
    (C * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta)
    (mul_nonneg hC.le (_root_.GD.N0232.N0719.N0972.d012342 k sizes hk hn theta).le) hbound
  have ho := _root_.GD.N0232.N0719.N0974.d019819 sizes (by omega)
    (fun i => by have := hn i; omega) theta e hem he hr.1
  exact (div_le_iff₀ (_root_.GD.N0232.N0719.N0972.d012342 k sizes hk hn theta)).mpr
    (by simpa [mul_comm] using ho.trans hr.2)

include hk hn in
theorem d028088
    (S : Set (_root_.GD.N0232.N0719.N0859.d010809 k))
    (hS : ∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ theta,
      _root_.GD.N0232.N0719.N0896.d011104 k g theta ∈ S ↔ theta ∈ S)
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) (hmem : ∀ᶠ j in atTop, theta j ∈ S)
    (hsat : Tendsto (fun j => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta j)) atTop (𝓝 1))
    (C : ℝ) (hC : 0 < C)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (hglobal : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes theta))
    (hlocal : ∀ theta ∈ S, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta)) : 1 ≤ C := by
  apply le_of_tendsto hsat
  filter_upwards [hmem] with j hj
  exact _root_.GD.N0027.N0284.d028087 k sizes hk hn S hS C hC
    f hf hglobal hlocal (theta j) hj

include hk in
theorem d028089 (active : Finset (Fin k)) (r : ℝ)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 active (_root_.GD.N0232.N0719.N0896.d011104 k g theta) ≤ r ↔
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ r := by
  exact _root_.GD.N0232.N0719.N0815.d010932 (by omega : 0 < k) active
    r g.shift g.d009239 g.d009240 theta

theorem d028090
    (active : Finset (Fin k)) (r : ℝ)
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hmem : ∀ᶠ j in atTop, _root_.GD.N0232.N0719.N0815.d010928 active (theta j) ≤ r)
    (hsat : Tendsto (fun j => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta j)) atTop (𝓝 1))
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn active r p = 1 := by
  have hupper : _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn active r p ≤ 1 :=
    iSup_le fun theta => _root_.GD.N0232.N0719.N0812.d011042 k sizes hk hn hp theta.1
  apply le_antisymm hupper
  by_contra h
  have hlt : _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn active r p < 1 := lt_of_not_ge h
  let v := (_root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn active r p).toReal
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hv1 : v < 1 := by
    simpa [v] using (ENNReal.toReal_lt_toReal
      (ne_top_of_le_ne_top ENNReal.one_ne_top hupper) ENNReal.one_ne_top).mpr hlt
  let C := (v + 1) / 2
  have hC : 0 < C := by dsimp [C]; linarith
  have hvC : v ≤ C := by dsimp [C]; linarith
  have hC1 : C < 1 := by dsimp [C]; linarith
  have hglobal : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) ≤
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes theta) := by
    intro theta
    rw [_root_.GD.N0232.N0719.N0896.d011093]
    exact (hp theta).trans ((_root_.GD.N0232.N0719.N0858.d010856 k sizes hk hn theta).le.trans
      (by rw [_root_.GD.N0232.N0719.N0859.d010823]; rfl))
  have hlocal : ∀ theta, _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ r →
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta) := by
    intro theta ht
    have hb : _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hn theta p ≤ ENNReal.ofReal C := by
      calc
        _ ≤ _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn active r p :=
          le_iSup (fun z : {theta : _root_.GD.N0232.N0719.N0859.d010809 k // _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ r} =>
            _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hn z.1 p) ⟨theta, ht⟩
        _ = ENNReal.ofReal v := (ENNReal.ofReal_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top hupper)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hvC
    change _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p / _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hn theta ≤ _ at hb
    have hb' := (ENNReal.div_le_iff (_root_.GD.N0232.N0719.N0858.d010854 k sizes hk hn theta).ne'
      ENNReal.ofReal_ne_top).mp hb
    rw [_root_.GD.N0232.N0719.N0896.d011093, ENNReal.ofReal_mul hC.le]
    exact hb'.trans (mul_le_mul_right (by
      exact (_root_.GD.N0232.N0719.N0858.d010856 k sizes hk hn theta).le.trans
        (by rw [_root_.GD.N0232.N0719.N0859.d010823]; rfl)) _)
  have hbad := _root_.GD.N0027.N0284.d028088 k sizes hk hn
    {theta | _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ r}
    (_root_.GD.N0027.N0284.d028089 k hk active r) theta hmem hsat C hC
    (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011089 k sizes p) hglobal hlocal
  exact (not_le_of_gt hC1) hbad

theorem d028091 :
    ∃ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
      p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn ∧ q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn ∧ p ≠ q := by
  let p := _root_.GD.N0232.N0719.N0935.d011165 k sizes hk hn
  let q := _root_.GD.N0232.N0719.N0859.d010820 k sizes hk hn
  have hpq : ∀ theta, _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p < _root_.GD.N0232.N0719.N0859.d010821 k sizes theta q :=
    _root_.GD.N0232.N0719.N0935.d011168
      k sizes hk hn
  refine ⟨p, q, (fun theta => (hpq theta).le.trans
    (_root_.GD.N0232.N0719.N0858.d010859 k sizes hk hn theta)), _root_.GD.N0232.N0719.N0858.d010859 k sizes hk hn, ?_⟩
  intro heq
  have hh := hpq (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [heq] at hh
  exact lt_irrefl _ hh

open _root_.GD.N0232.N0719.N0939

theorem d028092 (h : Fin k) {e : ℝ} (he : 0 < e) (i : Fin k) :
    e * _root_.GD.N0232.N0719.N0815.d010924 (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he) i =
      if i = h then (sizes i : ℝ)⁻¹ else e * (sizes i : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < sizes i := Nat.cast_pos.mpr (by have := hn i; omega)
  have hsq : (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he).scale i ^ 2 =
      _root_.GD.N0232.N0719.N0939.d020698 h e i * (sizes i : ℝ) :=
    (div_eq_iff hn0.ne').mp (_root_.GD.N0232.N0719.N0939.d020704 sizes hn h he i)
  unfold _root_.GD.N0232.N0719.N0815.d010924
  rw [hsq]
  by_cases hi : i = h
  · simp only [_root_.GD.N0232.N0719.N0939.d020698, hi, if_true]
    field_simp [he.ne']
  · simp [_root_.GD.N0232.N0719.N0939.d020698, hi]

theorem d028093
    (active : Finset (Fin k)) (h : Fin k) (hactive : h ∈ active)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun j => _root_.GD.N0232.N0719.N0815.d010928 active
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e j) (he j))) atTop (𝓝 0) := by
  classical
  let a : Fin k → ℝ := fun i => (sizes i : ℝ)⁻¹
  let N : ℝ → ℝ := fun x => ∑ i ∈ activeᶜ, if i = h then a i else x * a i
  let D : ℝ → ℝ := fun x => ∑ i, if i = h then a i else x * a i
  have hN : Continuous N := by
    apply continuous_finsetSum
    intro i hi
    by_cases hh : i = h <;> simp only [hh, if_true, if_false] <;> fun_prop
  have hD : Continuous D := by
    apply continuous_finsetSum
    intro i hi
    by_cases hh : i = h <;> simp only [hh, if_true, if_false] <;> fun_prop
  have hN0 : N 0 = 0 := by
    dsimp [N]
    apply Finset.sum_eq_zero
    intro i hi
    have hih : i ≠ h := by
      intro hh
      subst i
      exact (Finset.mem_compl.mp hi) hactive
    simp [hih]
  have hD0 : D 0 = a h := by simp [D]
  have hah : 0 < a h := by
    dsimp [a]
    exact inv_pos.mpr (Nat.cast_pos.mpr (by have := hn h; omega))
  have hlim : Tendsto (fun j => N (e j) / D (e j)) atTop (𝓝 0) := by
    have hratio := ((hN.continuousAt.div hD.continuousAt
      (by rw [hD0]; exact hah.ne')).tendsto).comp he0
    simpa only [Function.comp_def, Pi.div_apply, hN0, zero_div] using hratio
  convert hlim using 1
  funext j
  unfold _root_.GD.N0232.N0719.N0815.d010928 _root_.GD.N0232.N0719.N0815.d010926
  have heq := mul_div_mul_left
    (∑ i ∈ activeᶜ, _root_.GD.N0232.N0719.N0815.d010924 (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e j) (he j)) i)
    (∑ i, _root_.GD.N0232.N0719.N0815.d010924 (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e j) (he j)) i) (he j).ne'
  rw [← heq]
  simp_rw [Finset.mul_sum, _root_.GD.N0027.N0284.d028092 k sizes hn h (he j)]
  rfl

theorem d028094
    (hfour : ∀ i, 4 ≤ sizes i)
    (active : Finset (Fin k)) (hactive : active.Nonempty) (r : ℝ) (hr : 0 < r)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn active r p = 1 := by
  obtain ⟨h, hh⟩ := hactive
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he : ∀ j, 0 < e j := by intro j; dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hmass := _root_.GD.N0027.N0284.d028093 k sizes hn active h hh e he he0
  have hmem : ∀ᶠ j in atTop, _root_.GD.N0232.N0719.N0815.d010928 active
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e j) (he j)) ≤ r := by
    filter_upwards [hmass.eventually (gt_mem_nhds hr)] with j hj
    exact hj.le
  exact _root_.GD.N0027.N0284.d028090 k sizes hk hn active r _ hmem
    (_root_.GD.N0232.N0719.N0939.d020711 sizes hn h (fun i _ => hfour i) e he he0) p hp

theorem d028095
    (hfour : ∀ i, 4 ≤ sizes i) (c : _root_.GD.N0232.N0719.N0809.d010964 k)
    (hc : Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k c))
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn) :
    _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) p = 1 := by
  classical
  unfold _root_.GD.N0232.N0719.N0812.d011046
  suffices _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) p = 1 by
    rw [this, ENNReal.toReal_one]
  by_cases ha : c.1.Nonempty
  · exact _root_.GD.N0027.N0284.d028094 k sizes hk hn hfour c.1 ha _ (by
      unfold _root_.GD.N0232.N0719.N0815.d010938; positivity) p hp
  · have hempty : c.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hall : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0815.d010928 c.1 theta ≤ _root_.GD.N0232.N0719.N0815.d010938 c.2 := by
      obtain ⟨theta, htheta⟩ := hc
      have hi (eta : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0815.d010928 c.1 eta = 1 := by
        simp only [hempty, _root_.GD.N0232.N0719.N0815.d010928, Finset.compl_empty]
        exact div_self (_root_.GD.N0232.N0719.N0815.d010927 (by omega : 0 < k) eta).ne'
      rw [hi theta] at htheta
      intro eta
      rw [hi eta]
      exact htheta
    let h : Fin k := ⟨0, by omega⟩
    let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    have he : ∀ j, 0 < e j := by intro j; dsimp [e]; positivity
    have he0 : Tendsto e atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact _root_.GD.N0027.N0284.d028090 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2)
      (fun j => _root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e j) (he j))
      (Eventually.of_forall fun j => hall _)
      (_root_.GD.N0232.N0719.N0939.d020711 sizes hn h (fun i _ => hfour i) e he he0) p hp

theorem d028096
    (hfour : ∀ i, 4 ≤ sizes i) (c : _root_.GD.N0232.N0719.N0809.d010964 k)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn) (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn) :
    _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) p =
      _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) q := by
  classical
  by_cases hc : Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k c)
  · rw [_root_.GD.N0027.N0284.d028095 k sizes hk hn hfour c hc p hp,
      _root_.GD.N0027.N0284.d028095 k sizes hk hn hfour c hc q hq]
  · haveI : IsEmpty (_root_.GD.N0232.N0719.N0810.d011629 k c) := not_nonempty_iff.mp hc
    have hz (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
        _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) d = 0 := by
      change (⨆ theta : _root_.GD.N0232.N0719.N0810.d011629 k c,
        _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hn theta.1 d) = 0
      simp
    simp only [_root_.GD.N0232.N0719.N0812.d011046, hz]

theorem d028097
    (hfour : ∀ i, 4 ≤ sizes i) (c : _root_.GD.N0232.N0719.N0809.d010964 k)
    (hc : Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k c))
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn) (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ theta : _root_.GD.N0232.N0719.N0810.d011629 k c,
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hn theta.1 p q < epsilon ∧
      1 - _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hn theta.1 p < 2 * epsilon ∧
      1 - _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hn theta.1 q < 2 * epsilon := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn := by
    unfold _root_.GD.N0230.N0718.d001528
    exact (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hn) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hP := _root_.GD.N0232.N0719.N0812.d011048 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) hp hc
  have hQ := _root_.GD.N0232.N0719.N0812.d011048 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) hq hc
  have hM := _root_.GD.N0232.N0719.N0812.d011048 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) hmid hc
  have heq (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn) :=
    _root_.GD.N0027.N0284.d028095 k sizes hk hn hfour c hc d hd
  have hz : _root_.GD.N0230.N0554.d001563
      (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2)) p q = 0 := by
    unfold _root_.GD.N0230.N0554.d001563
    rw [heq p hp, heq q hq, heq _ hmid]
    norm_num
  have h := (_root_.GD.N0230.N0651.d001589
    (fun theta : _root_.GD.N0232.N0719.N0810.d011629 k c =>
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hn theta.1)
    (fun theta : _root_.GD.N0232.N0719.N0810.d011629 k c =>
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hn theta.1)
    (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hn c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2)) p q hM
    (fun theta => _root_.GD.N0232.N0719.N0811.d011040
      k sizes hk hn theta.1 hp hq)
    (fun theta => _root_.GD.N0232.N0719.N0811.d011039
      k sizes hk hn theta.1 p q)
    (fun theta => hP.1 ⟨theta, rfl⟩) (fun theta => hQ.1 ⟨theta, rfl⟩)).mp hz epsilon hepsilon
  simpa only [heq p hp, heq q hq] using h

theorem d028098
    (hfour : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hn := by
  apply (_root_.GD.N0232.N0719.N0824.d011726
    k sizes hk hn).mp
  intro hres
  obtain ⟨p, q, hp, hq, hpq⟩ := _root_.GD.N0027.N0284.d028091 k sizes hk hn
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hn := by
    unfold _root_.GD.N0230.N0718.d001528
    exact (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hn) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hsep := (_root_.GD.N0232.N0719.N0823.d011715
    k sizes hk hn (_root_.GD.N0232.N0719.N0809.d010966 k)).mp hres
  obtain ⟨j, hj, hlt⟩ := hsep p q ⟨hp, hq, fun j =>
    _root_.GD.N0027.N0284.d028096 k sizes hk hn hfour (_root_.GD.N0232.N0719.N0809.d010966 k j)
      p q hp hq⟩ hpq
  change _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hn _ _ (_root_.GD.N0230.N0718.d001528 p q) <
    _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hn _ _ p at hlt
  rw [_root_.GD.N0027.N0284.d028095 k sizes hk hn hfour
      (_root_.GD.N0232.N0719.N0809.d010966 k j) hj (_root_.GD.N0230.N0718.d001528 p q) hmid,
    _root_.GD.N0027.N0284.d028095 k sizes hk hn hfour
      (_root_.GD.N0232.N0719.N0809.d010966 k j) hj p hp] at hlt
  exact lt_irrefl _ hlt

theorem d028099 :
    _root_.GD.N0232.N0719.N0824.d011722 3 (fun _ => 4)
      (by norm_num) (by intro _; norm_num) :=
  _root_.GD.N0027.N0284.d028098 3 (fun _ => 4)
    (by norm_num) (by intro _; norm_num) (by intro _; norm_num)

theorem d028100 :
    ¬ (∀ (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i),
      ¬ _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hn) := by
  intro h
  exact h 3 (fun _ => 4) (by norm_num) (by intro _; norm_num)
    _root_.GD.N0027.N0284.d028099

end
end GD.N0027.N0284

#print axioms _root_.GD.N0027.N0284.d028087
#print axioms _root_.GD.N0027.N0284.d028088
#print axioms _root_.GD.N0027.N0284.d028090
#print axioms _root_.GD.N0027.N0284.d028091
#print axioms _root_.GD.N0027.N0284.d028093
#print axioms _root_.GD.N0027.N0284.d028094
#print axioms _root_.GD.N0027.N0284.d028095
#print axioms _root_.GD.N0027.N0284.d028096
#print axioms _root_.GD.N0027.N0284.d028097
#print axioms _root_.GD.N0027.N0284.d028098
#print axioms _root_.GD.N0027.N0284.d028099
#print axioms _root_.GD.N0027.N0284.d028100
