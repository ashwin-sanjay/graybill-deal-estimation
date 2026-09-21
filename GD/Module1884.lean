import GD.Module1883
import GD.Module1507
import GD.Module1409
import GD.Module1722
import GD.Module1543

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0206.N0445
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1332 _root_.GD.N0232.N0720.N1328
open _root_.GD.N0096.N0344
open _root_.GD.N0206.N0448 _root_.GD.N0206.N0447 _root_.GD.N0206.N0450

theorem d030697
    {m n : ℕ} {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n) {C : ℝ}
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta))
    (ha : _root_.GD.N0206.N0448.d022618 m n d) : _root_.GD.N0096.N0344.d030491 m n d := by
  have hf (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hcap theta)
  refine ⟨hd.1, ?_, hf, _root_.GD.N0206.N0448.d022620 m n hd.1 (hf _) ha⟩
  intro g x
  exact hd.2 g.shift g.d009239 (Real.exp_pos _) x

theorem d030698
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ¬ _root_.GD.N0206.N0448.d022618 m n d := by
  intro ha
  have ht := _root_.GD.N0206.N0445.d030697 hd hcap ha
  have hbound := _root_.GD.N0206.N0447.d030696 hm hn ht (by norm_num) hcap
  apply _root_.GD.N0206.N0450.d023510 hm hn
  intro p hp
  simpa only [_root_.GD.N0232.N0720.N1332.d020106, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hbound ⟨p, hp⟩

theorem d030699
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hsmall : m ≤ 3 ∨ n ≤ 3)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ¬ _root_.GD.N0206.N0448.d022618 m n d := by
  intro ha
  have ht := _root_.GD.N0206.N0445.d030697 hd hcap ha
  have hbound := _root_.GD.N0206.N0447.d030696 hm hn ht hC hcap
  apply _root_.GD.N0206.N0450.d023511 hm hn hsmall C hC
  intro p hp
  have h := hbound ⟨p, hp⟩
  change _root_.GD.N0232.N0720.N1332.d020106 m n
    (fun x => _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) p ≤
      C * p * (1 - p)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : C - 1 ≤ C) hp.1.le)
    (sub_nonneg.mpr hp.2.le))

theorem d030700
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n)
    (ha : _root_.GD.N0206.N0448.d022618 m n d) : 2 < _root_.GD.N0232.N0720.N1256.d015548 m n d := by
  by_contra! h
  apply _root_.GD.N0206.N0445.d030698 hm hn hd ?_ ha
  intro theta
  apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) 2 (by norm_num) theta d).mp
  have htheta := (le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta).trans h
  simpa using htheta

theorem d030701
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hsmall : m ≤ 3 ∨ n ≤ 3)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n)
    (ha : _root_.GD.N0206.N0448.d022618 m n d) : _root_.GD.N0232.N0720.N1256.d015548 m n d = ⊤ := by
  by_contra hf
  let C := (_root_.GD.N0232.N0720.N1256.d015548 m n d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  apply _root_.GD.N0206.N0445.d030699 hm hn hsmall hd hC ?_ ha
  intro theta
  apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta d).mp
  rw [show ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015548 m n d from ENNReal.ofReal_toReal hf]
  exact le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta

theorem d030702
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n)
    (hv : _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n) :
    ¬ _root_.GD.N0206.N0448.d022618 m n d := by
  intro ha
  by_cases hsmall : m ≤ 3 ∨ n ≤ 3
  · exact hfinite (hv.symm.trans (_root_.GD.N0206.N0445.d030701 hm hn hsmall hd ha))
  · have hm3 : 3 ≤ m := by omega
    have hn3 : 3 ≤ n := by omega
    have hgt := _root_.GD.N0206.N0445.d030700 hm hn hd ha
    rw [hv] at hgt
    exact (not_le_of_gt hgt) (_root_.GD.N0098.d028729 m n hm3 hn3)


theorem d030703
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdesign : 4 ≤ (m - 1) * (n - 1)) :
    ¬ ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n ∧ _root_.GD.N0206.N0448.d022618 m n d ∧
        _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  rintro ⟨d, hd, ha, hv⟩
  exact _root_.GD.N0206.N0445.d030702 hm hn
    ((_root_.GD.N0067.d023923 m n hm hn).mpr hdesign) hd hv ha

theorem d030704
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    (∃ d ∈ _root_.GD.N0232.N0720.N1256.d015552 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n ∧ ¬ _root_.GD.N0206.N0448.d022618 m n d) ∧
    (∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n ∧ _root_.GD.N0206.N0448.d022618 m n d ∧
        d ∉ _root_.GD.N0232.N0720.N1256.d015546 m n) := by
  constructor
  · obtain ⟨d, hd, hv⟩ := _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
    exact ⟨d, hd, hv, _root_.GD.N0206.N0445.d030702 hm hn hfinite hd.1 hv⟩
  · obtain ⟨d, hd, ht, hv⟩ := _root_.GD.N0098.d028161 m n hm hn
    have ha : _root_.GD.N0206.N0448.d022618 m n d := _root_.GD.N0206.N0448.d022621 m n ht
    exact ⟨d, hd, hv, ha, fun he =>
      _root_.GD.N0206.N0445.d030702 hm hn hfinite he hv ha⟩

theorem d030705
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    min (theta.scale₁ ^ 2 / (m : ℝ)) (theta.scale₂ ^ 2 / (n : ℝ)) ≤
      2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta := by
  let a := theta.scale₁ ^ 2 / (m : ℝ)
  let b := theta.scale₂ ^ 2 / (n : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := div_pos (sq_pos_of_pos theta.scale₁_pos) hmR
  have hb : 0 < b := div_pos (sq_pos_of_pos theta.scale₂_pos) hnR
  have ho : _root_.GD.N0232.N0720.N1257.d015508 m n theta = a * b / (a + b) := by
    have hi : _root_.GD.N0232.N0720.N1257.d015508 m n theta = (a⁻¹ + b⁻¹)⁻¹ := by
      simp only [a, b, inv_div, _root_.GD.N0232.N0720.N1257.d015508]
    rw [hi]
    field_simp [ha.ne', hb.ne', (add_pos ha hb).ne']
    ring
  change min a b ≤ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta
  rw [ho, ← mul_div_assoc]
  apply (le_div_iff₀ (add_pos ha hb)).mpr
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    nlinarith [mul_le_mul_of_nonneg_left hab ha.le]
  · rw [min_eq_right hba]
    nlinarith [mul_le_mul_of_nonneg_left hba hb.le]


theorem d030706
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n)
    (hfirst : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (theta.scale₁ ^ 2 / (m : ℝ)))
    (hsecond : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (theta.scale₂ ^ 2 / (n : ℝ))) :
    ¬ _root_.GD.N0206.N0448.d022618 m n d := by
  apply _root_.GD.N0206.N0445.d030698 hm hn hd
  intro theta
  have hmin : _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (min (theta.scale₁ ^ 2 / (m : ℝ)) (theta.scale₂ ^ 2 / (n : ℝ))) := by
    rcases le_total (theta.scale₁ ^ 2 / (m : ℝ)) (theta.scale₂ ^ 2 / (n : ℝ)) with h | h
    · rw [min_eq_left h]
      exact hfirst theta
    · rw [min_eq_right h]
      exact hsecond theta
  exact hmin.trans (ENNReal.ofReal_le_ofReal (_root_.GD.N0206.N0445.d030705 hm hn theta))

end
end GD.N0206.N0445

#print axioms _root_.GD.N0206.N0445.d030697
#print axioms _root_.GD.N0206.N0445.d030698
#print axioms _root_.GD.N0206.N0445.d030699
#print axioms _root_.GD.N0206.N0445.d030700
#print axioms _root_.GD.N0206.N0445.d030701
#print axioms _root_.GD.N0206.N0445.d030702
#print axioms _root_.GD.N0206.N0445.d030703
#print axioms _root_.GD.N0206.N0445.d030704
#print axioms _root_.GD.N0206.N0445.d030705
#print axioms _root_.GD.N0206.N0445.d030706
