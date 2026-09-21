import GD.Module1107
import GD.Module1014

































open Filter Set Topology
open scoped Topology

namespace GD.N0232.N0720.N1294

noncomputable section

open _root_.GD.N0232.N0720.N1350
open _root_.GD.N0232.N0720.N1293
open _root_.GD.N0232.N0720.N1492




def d017799 (alpha : ℝ) : ℝ := 5 / 2 - alpha



def d017800 (alpha e : ℝ) : ℝ :=
  e ^ _root_.GD.N0232.N0720.N1294.d017799 alpha /
    (e ^ _root_.GD.N0232.N0720.N1294.d017799 alpha + (1 - e) ^ _root_.GD.N0232.N0720.N1294.d017799 alpha)

theorem d017801 (alpha : ℝ) :
    _root_.GD.N0232.N0720.N1294.d017799 alpha = 1 ↔ alpha = 3 / 2 := by
  unfold _root_.GD.N0232.N0720.N1294.d017799
  constructor <;> intro h <;> linarith



theorem d017802
    {e : ℝ} (_he : e ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1294.d017800 (3 / 2) e = e := by
  unfold _root_.GD.N0232.N0720.N1294.d017800 _root_.GD.N0232.N0720.N1294.d017799
  norm_num

private theorem d017803
    {p : ℝ}
    (h : (1 / 4 : ℝ) ^ p /
        ((1 / 4 : ℝ) ^ p + (1 - 1 / 4 : ℝ) ^ p) = 1 / 4) :
    p = 1 := by
  let a : ℝ := (1 / 4 : ℝ) ^ p
  let b : ℝ := (3 / 4 : ℝ) ^ p
  have ha : 0 < a := by
    dsimp [a]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hb : 0 < b := by
    dsimp [b]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hden : a + b ≠ 0 := (add_pos ha hb).ne'
  have hab : b = 3 * a := by
    have htail : 1 - (1 / 4 : ℝ) = 3 / 4 := by norm_num
    rw [htail] at h
    change a / (a + b) = 1 / 4 at h
    field_simp [hden] at h
    linarith
  have hratio : b / a = 3 := by
    rw [hab]
    field_simp [ha.ne']
  have hpow : (3 : ℝ) ^ p = 3 := by
    have hdiv : (3 / 4 : ℝ) ^ p / (1 / 4 : ℝ) ^ p = 3 := by
      simpa [a, b] using hratio
    rw [← Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hdiv
    norm_num at hdiv ⊢
    exact hdiv
  have hpowOne : (3 : ℝ) ^ (1 : ℝ) = 3 := Real.rpow_one 3
  exact (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 3)).injective
    (by simpa [hpowOne] using hpow)




theorem d017804
    {alpha : ℝ}
    (htrace : ∀ e ∈ Ioo (0 : ℝ) 1,
      _root_.GD.N0232.N0720.N1294.d017800 alpha e = e) :
    alpha = 3 / 2 := by
  have hquarter := htrace (1 / 4) (by constructor <;> norm_num)
  unfold _root_.GD.N0232.N0720.N1294.d017800 at hquarter
  have hp : _root_.GD.N0232.N0720.N1294.d017799 alpha = 1 :=
    _root_.GD.N0232.N0720.N1294.d017803 hquarter
  exact (_root_.GD.N0232.N0720.N1294.d017801 alpha).1 hp

theorem d017805 (alpha : ℝ) :
    (∀ e ∈ Ioo (0 : ℝ) 1, _root_.GD.N0232.N0720.N1294.d017800 alpha e = e) ↔
      alpha = 3 / 2 := by
  constructor
  · exact _root_.GD.N0232.N0720.N1294.d017804
  · intro h e he
    subst alpha
    exact _root_.GD.N0232.N0720.N1294.d017802 he





def d017806 (q e F : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1492.d016123 e F q



theorem d017807
    (a b r E F : ℝ) :
    _root_.GD.N0232.N0720.N1294.d017806 (a * b * r) (a * E) F =
      a * (E + (1 + F) * b * r) -
        a ^ 2 * (2 * b * E * r + F * b ^ 2 * r ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1294.d017806 _root_.GD.N0232.N0720.N1492.d016123
  ring




theorem d017808
    (lambda r E F : ℝ) (n ell : ℕ) :
    _root_.GD.N0232.N0720.N1294.d017806
        (lambda ^ n * lambda ^ ell * r) (lambda ^ n * E) F =
      lambda ^ n * (E + (1 + F) * lambda ^ ell * r) -
        (lambda ^ n) ^ 2 *
          (2 * lambda ^ ell * E * r +
            F * (lambda ^ ell) ^ 2 * r ^ 2) := by
  exact _root_.GD.N0232.N0720.N1294.d017807
    (lambda ^ n) (lambda ^ ell) r E F



def d017809 (lambda w : ℝ) (k : ℕ) : ℝ :=
  lambda ^ ((3 / 2 : ℝ) * (k : ℝ)) * w



theorem d017810
    {lambda : ℝ} (hlambda : 0 < lambda) (w : ℝ) (k : ℕ) :
    _root_.GD.N0232.N0720.N1294.d017809 lambda w (k + 1) =
      lambda ^ (3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1294.d017809 lambda w k := by
  unfold _root_.GD.N0232.N0720.N1294.d017809
  rw [show (3 / 2 : ℝ) * ((k + 1 : ℕ) : ℝ) =
      3 / 2 + (3 / 2 : ℝ) * (k : ℝ) by
      push_cast
      ring,
    Real.rpow_add hlambda]
  ring







def d017811 (rho C : ℝ) (n : ℕ) : ℝ :=
  1 / (1 + C * rho ^ n) ^ (5 / 2 : ℝ)




theorem d017812
    {rho C : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    Tendsto (_root_.GD.N0232.N0720.N1294.d017811 rho C) atTop (nhds 1) := by
  have hpow : Tendsto (fun n : ℕ ↦ rho ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrho0 hrho1
  have hcont : ContinuousAt
      (fun z : ℝ ↦ 1 / (1 + C * z) ^ (5 / 2 : ℝ)) 0 := by
    fun_prop (disch := norm_num)
  have h := hcont.tendsto.comp hpow
  unfold _root_.GD.N0232.N0720.N1294.d017811
  simpa [Function.comp_def] using h




theorem d017813
    {rho C : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    ¬ Summable (_root_.GD.N0232.N0720.N1294.d017811 rho C) := by
  intro hsum
  have hzero : Tendsto (_root_.GD.N0232.N0720.N1294.d017811 rho C) atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hone := _root_.GD.N0232.N0720.N1294.d017812 (C := C) hrho0 hrho1
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this



theorem d017814
    {rho beta x : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (hbetaNe : beta ≠ 3 / 2) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1350.d002729 rho beta (rho * x) ≠
      _root_.GD.N0232.N0720.N1350.d002729 rho beta x / rho :=
  _root_.GD.N0232.N0720.N1350.d002736
    hrho hrhoOne hbeta hbetaTop hbetaNe hx




theorem d017815 :
    _root_.GD.N0232.N0720.N1294.d017799 (3 / 2) = 1 ∧
      _root_.GD.N0232.N0720.N1350.d002732 (1 / 256) (3 / 2) 1 (16 / 17) (16 / 17) ≠ 16 / 17 := by
  constructor
  · exact (_root_.GD.N0232.N0720.N1294.d017801 (3 / 2)).2 rfl
  · exact _root_.GD.N0232.N0720.N1293.d017797

end


end GD.N0232.N0720.N1294

#print axioms _root_.GD.N0232.N0720.N1294.d017805
#print axioms _root_.GD.N0232.N0720.N1294.d017808
#print axioms _root_.GD.N0232.N0720.N1294.d017810
#print axioms _root_.GD.N0232.N0720.N1294.d017813
#print axioms _root_.GD.N0232.N0720.N1294.d017815
