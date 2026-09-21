import GD.Module0276
import Mathlib.RingTheory.PowerSeries.Basic




















open MeasureTheory Set
open scoped BigOperators Polynomial

namespace GD.N0232.N0720.N1415

noncomputable section


def d004071 (q : ℝ) (n : ℕ) : ℝ :=
  (∏ i ∈ Finset.range n, (q + (i : ℝ))) / (n.factorial : ℝ)

@[simp]
theorem d004072 (q : ℝ) :
    _root_.GD.N0232.N0720.N1415.d004071 q 0 = 1 := by
  simp [_root_.GD.N0232.N0720.N1415.d004071]

@[simp]
theorem d004073 (q : ℝ) :
    _root_.GD.N0232.N0720.N1415.d004071 q 1 = q := by
  simp [_root_.GD.N0232.N0720.N1415.d004071]

theorem d004074 {q : ℝ} (hq : 0 < q) (n : ℕ) :
    0 < _root_.GD.N0232.N0720.N1415.d004071 q n := by
  apply div_pos
  · exact Finset.prod_pos fun i _ ↦
      add_pos_of_pos_of_nonneg hq (Nat.cast_nonneg i)
  · exact_mod_cast Nat.factorial_pos n


def d004075 (q : ℝ) (j : ℕ) (mu : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ _root_.GD.N0232.N0720.N1415.d004071 q n * mu (n + j)

@[simp]
theorem d004076 (q : ℝ) (j n : ℕ) (mu : ℕ → ℝ) :
    PowerSeries.coeff n (_root_.GD.N0232.N0720.N1415.d004075 q j mu) =
      _root_.GD.N0232.N0720.N1415.d004071 q n * mu (n + j) :=
  PowerSeries.coeff_mk n _

@[simp]
theorem d004077 (q : ℝ) (j : ℕ) (mu : ℕ → ℝ) :
    PowerSeries.constantCoeff (_root_.GD.N0232.N0720.N1415.d004075 q j mu) = mu j := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, _root_.GD.N0232.N0720.N1415.d004076]
  simp





def d004078 (q : ℝ) (mu : ℕ → ℝ) : PowerSeries ℝ :=
  (_root_.GD.N0232.N0720.N1415.d004075 q 0 mu) ^ 3 * _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 mu -
    PowerSeries.C (3 : ℝ) *
      (_root_.GD.N0232.N0720.N1415.d004075 q 1 mu * (_root_.GD.N0232.N0720.N1415.d004075 q 0 mu) ^ 2 *
        _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 2 mu) +
    PowerSeries.C (3 : ℝ) *
      ((_root_.GD.N0232.N0720.N1415.d004075 q 1 mu) ^ 2 * _root_.GD.N0232.N0720.N1415.d004075 q 0 mu *
        _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 1 mu) -
    (_root_.GD.N0232.N0720.N1415.d004075 q 1 mu) ^ 3 * _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 0 mu


theorem d004079 (q : ℝ) (mu : ℕ → ℝ)
    (hmu0 : mu 0 = 1) (hmu1 : mu 1 = 0)
    (hcubic : _root_.GD.N0232.N0720.N1415.d004078 q mu = 0) : mu 3 = 0 := by
  have h := congrArg PowerSeries.constantCoeff hcubic
  simpa [_root_.GD.N0232.N0720.N1415.d004078, hmu0, hmu1] using h


theorem d004080 (q : ℝ) (mu : ℕ → ℝ)
    (hmu0 : mu 0 = 1) (hmu1 : mu 1 = 0)
    (hcubic : _root_.GD.N0232.N0720.N1415.d004078 q mu = 0) :
    (q + 1) * mu 4 = 3 * q * (mu 2) ^ 2 := by
  have h := congrArg (PowerSeries.coeff 1) hcubic
  simp [_root_.GD.N0232.N0720.N1415.d004078, PowerSeries.coeff_one_mul,
    PowerSeries.coeff_one_pow, hmu0, hmu1] at h
  nlinarith [h]


theorem d004081 (mu : ℕ → ℝ)
    (hmu0 : mu 0 = 1) (hmu1 : mu 1 = 0)
    (hcubic : _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ) mu = 0) :
    7 * mu 4 = 15 * (mu 2) ^ 2 := by
  have h := _root_.GD.N0232.N0720.N1415.d004080 (5 / 2 : ℝ) mu hmu0 hmu1 hcubic
  nlinarith [h]


def d004082 (n : ℕ) (f g : PowerSeries ℝ) : Prop :=
  ∀ i ≤ n, PowerSeries.coeff i f = PowerSeries.coeff i g

theorem d004083 (n : ℕ) (f : PowerSeries ℝ) : _root_.GD.N0232.N0720.N1415.d004082 n f f := by
  intro i hi
  rfl

theorem d004084 {n : ℕ} {f f' g g' : PowerSeries ℝ}
    (hf : _root_.GD.N0232.N0720.N1415.d004082 n f f') (hg : _root_.GD.N0232.N0720.N1415.d004082 n g g') :
    _root_.GD.N0232.N0720.N1415.d004082 n (f * g) (f' * g') := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hij' : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega), hg ij.2 (by omega)]

theorem d004085 {n : ℕ} {f g : PowerSeries ℝ}
    (h : _root_.GD.N0232.N0720.N1415.d004082 n f g) (k : ℕ) : _root_.GD.N0232.N0720.N1415.d004082 n (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact _root_.GD.N0232.N0720.N1415.d004083 n 1
  | succ k ih =>
      simpa only [pow_succ] using _root_.GD.N0232.N0720.N1415.d004084 ih h



theorem d004086 (n : ℕ) (f g : PowerSeries ℝ)
    (hg : ∀ i < n, PowerSeries.coeff i g = 0) :
    PowerSeries.coeff n (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff n g := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_single (0, n)
  · rintro ⟨i, j⟩ hij hne
    have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
    have hj : j < n := by
      by_contra hnot
      have hi : i = 0 := by omega
      have hjn : j = n := by omega
      exact hne (by simp [hi, hjn])
    rw [hg j hj, mul_zero]
  · intro hnot
    exact (hnot (by simp)).elim



theorem d004087 (q : ℝ) (mu nu : ℕ → ℝ) (n : ℕ)
    (hmu0 : mu 0 = 1)
    (hprev : ∀ i ≤ n + 2, mu i = nu i) :
    PowerSeries.coeff n (_root_.GD.N0232.N0720.N1415.d004078 q mu) -
        PowerSeries.coeff n (_root_.GD.N0232.N0720.N1415.d004078 q nu) =
      _root_.GD.N0232.N0720.N1415.d004071 (q + 1) n * (mu (n + 3) - nu (n + 3)) := by
  have hjet (p : ℝ) (j : ℕ) (hj : j ≤ 2) :
      _root_.GD.N0232.N0720.N1415.d004082 n (_root_.GD.N0232.N0720.N1415.d004075 p j mu) (_root_.GD.N0232.N0720.N1415.d004075 p j nu) := by
    intro i hi
    rw [_root_.GD.N0232.N0720.N1415.d004076, _root_.GD.N0232.N0720.N1415.d004076, hprev (i + j) (by omega)]
  have hmass := hjet q 0 (by omega)
  have hfirst := hjet q 1 (by omega)
  have hsecondTerm :=
    _root_.GD.N0232.N0720.N1415.d004084 (_root_.GD.N0232.N0720.N1415.d004084 hfirst (_root_.GD.N0232.N0720.N1415.d004085 hmass 2))
      (hjet (q + 1) 2 (by omega))
  have hthirdTerm :=
    _root_.GD.N0232.N0720.N1415.d004084 (_root_.GD.N0232.N0720.N1415.d004084 (_root_.GD.N0232.N0720.N1415.d004085 hfirst 2) hmass)
      (hjet (q + 1) 1 (by omega))
  have hfourthTerm :=
    _root_.GD.N0232.N0720.N1415.d004084 (_root_.GD.N0232.N0720.N1415.d004085 hfirst 3) (hjet (q + 1) 0 (by omega))
  have hsameLeft :=
    _root_.GD.N0232.N0720.N1415.d004084 (_root_.GD.N0232.N0720.N1415.d004085 hmass 3)
      (_root_.GD.N0232.N0720.N1415.d004083 n (_root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 nu))
  have hlow : ∀ i < n,
      PowerSeries.coeff i
        (_root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 mu - _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 nu) = 0 := by
    intro i hi
    rw [map_sub, _root_.GD.N0232.N0720.N1415.d004076, _root_.GD.N0232.N0720.N1415.d004076,
      hprev (i + 3) (by omega), sub_self]
  have hlead := _root_.GD.N0232.N0720.N1415.d004086 n
    ((_root_.GD.N0232.N0720.N1415.d004075 q 0 mu) ^ 3)
    (_root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 mu - _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 nu) hlow
  have hconstant :
      PowerSeries.coeff 0 ((_root_.GD.N0232.N0720.N1415.d004075 q 0 mu) ^ 3) = 1 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hmu0]
  rw [hconstant, one_mul, mul_sub, map_sub, map_sub,
    _root_.GD.N0232.N0720.N1415.d004076, _root_.GD.N0232.N0720.N1415.d004076] at hlead
  have htop :
      PowerSeries.coeff n
          ((_root_.GD.N0232.N0720.N1415.d004075 q 0 mu) ^ 3 * _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 mu) -
        PowerSeries.coeff n
          ((_root_.GD.N0232.N0720.N1415.d004075 q 0 nu) ^ 3 * _root_.GD.N0232.N0720.N1415.d004075 (q + 1) 3 nu) =
        _root_.GD.N0232.N0720.N1415.d004071 (q + 1) n * (mu (n + 3) - nu (n + 3)) := by
    rw [← hsameLeft n le_rfl]
    calc
      _ = _root_.GD.N0232.N0720.N1415.d004071 (q + 1) n * mu (n + 3) -
          _root_.GD.N0232.N0720.N1415.d004071 (q + 1) n * nu (n + 3) := hlead
      _ = _ := (mul_sub _ _ _).symm
  simp only [_root_.GD.N0232.N0720.N1415.d004078, map_sub, map_add, PowerSeries.coeff_C_mul]
  rw [hsecondTerm n le_rfl, hthirdTerm n le_rfl, hfourthTerm n le_rfl]
  linarith [htop]


theorem d004088
    {q : ℝ} (hq : 0 < q + 1) (mu nu : ℕ → ℝ) (n : ℕ)
    (hmu0 : mu 0 = 1)
    (hprev : ∀ i ≤ n + 2, mu i = nu i)
    (hmu : _root_.GD.N0232.N0720.N1415.d004078 q mu = 0)
    (hnu : _root_.GD.N0232.N0720.N1415.d004078 q nu = 0) :
    mu (n + 3) = nu (n + 3) := by
  have h := _root_.GD.N0232.N0720.N1415.d004087 q mu nu n hmu0 hprev
  rw [hmu, hnu, map_zero, sub_self] at h
  have hcoef : _root_.GD.N0232.N0720.N1415.d004071 (q + 1) n ≠ 0 :=
    ne_of_gt (_root_.GD.N0232.N0720.N1415.d004074 hq n)
  have hdiff : mu (n + 3) - nu (n + 3) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left hcoef
  exact sub_eq_zero.mp hdiff



theorem d004089
    {q : ℝ} (hq : 0 < q + 1) (mu nu : ℕ → ℝ)
    (hmu0 : mu 0 = 1) (hnu0 : nu 0 = 1)
    (hfirst : mu 1 = nu 1) (hsecond : mu 2 = nu 2)
    (hmu : _root_.GD.N0232.N0720.N1415.d004078 q mu = 0)
    (hnu : _root_.GD.N0232.N0720.N1415.d004078 q nu = 0) :
    mu = nu := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 3
      · interval_cases n
        · exact hmu0.trans hnu0.symm
        · exact hfirst
        · exact hsecond
      · let k := n - 3
        have hnk : n = k + 3 := by dsimp [k]; omega
        rw [hnk]
        apply _root_.GD.N0232.N0720.N1415.d004088 hq mu nu k hmu0
          (fun i hi ↦ ih i (by omega)) hmu hnu


theorem d004090
    (mu nu : ℕ → ℝ)
    (hmu0 : mu 0 = 1) (hnu0 : nu 0 = 1)
    (hfirst : mu 1 = nu 1) (hsecond : mu 2 = nu 2)
    (hmu : _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ) mu = 0)
    (hnu : _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ) nu = 0) :
    mu = nu :=
  _root_.GD.N0232.N0720.N1415.d004089 (by norm_num) mu nu
    hmu0 hnu0 hfirst hsecond hmu hnu

section CompactMeasures

variable (a b center : ℝ)



def d004091 (mu : Measure (Set.Icc a b)) (n : ℕ) : ℝ :=
  ∫ x, ((x : ℝ) - center) ^ n ∂mu

private theorem d004092
    (mu : Measure (Set.Icc a b)) [IsFiniteMeasure mu] (p : ℝ[X]) :
    Integrable (fun x : Set.Icc a b ↦ p.eval ((x : ℝ) - center)) mu := by
  have hcont :
      Continuous (fun x : Set.Icc a b ↦ p.eval ((x : ℝ) - center)) := by
    fun_prop
  exact hcont.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact



theorem d004093
    (mu nu : Measure (Set.Icc a b))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmoment : ∀ n,
      _root_.GD.N0232.N0720.N1415.d004091 a b center mu n = _root_.GD.N0232.N0720.N1415.d004091 a b center nu n) :
    mu = nu := by
  have hshift : ∀ p : ℝ[X],
      (∫ x : Set.Icc a b, p.eval ((x : ℝ) - center) ∂mu) =
        ∫ x : Set.Icc a b, p.eval ((x : ℝ) - center) ∂nu := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [Polynomial.eval_add]
        rw [integral_add (_root_.GD.N0232.N0720.N1415.d004092 a b center mu p)
            (_root_.GD.N0232.N0720.N1415.d004092 a b center mu q),
          integral_add (_root_.GD.N0232.N0720.N1415.d004092 a b center nu p)
            (_root_.GD.N0232.N0720.N1415.d004092 a b center nu q), hp, hq]
    | monomial n c =>
        simp only [Polynomial.eval_monomial]
        rw [integral_const_mul, integral_const_mul]
        exact congrArg (c * ·) (hmoment n)
  apply _root_.GD.N0235.N0743.d004070
    a b mu nu
  intro p
  have hp := hshift (p.comp (Polynomial.X + Polynomial.C center))
  simp only [Polynomial.eval_comp] at hp
  simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    sub_add_cancel] using hp



theorem d004094
    {q : ℝ} (hq : 0 < q + 1)
    (mu nu : Measure (Set.Icc a b))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hfirst : _root_.GD.N0232.N0720.N1415.d004091 a b center mu 1 = _root_.GD.N0232.N0720.N1415.d004091 a b center nu 1)
    (hsecond : _root_.GD.N0232.N0720.N1415.d004091 a b center mu 2 = _root_.GD.N0232.N0720.N1415.d004091 a b center nu 2)
    (hmu : _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 a b center mu) = 0)
    (hnu : _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 a b center nu) = 0) :
    mu = nu := by
  apply _root_.GD.N0232.N0720.N1415.d004093 a b center mu nu
  have hzeroMu : _root_.GD.N0232.N0720.N1415.d004091 a b center mu 0 = 1 := by
    simp [_root_.GD.N0232.N0720.N1415.d004091]
  have hzeroNu : _root_.GD.N0232.N0720.N1415.d004091 a b center nu 0 = 1 := by
    simp [_root_.GD.N0232.N0720.N1415.d004091]
  have hall := _root_.GD.N0232.N0720.N1415.d004089 hq
    (_root_.GD.N0232.N0720.N1415.d004091 a b center mu) (_root_.GD.N0232.N0720.N1415.d004091 a b center nu)
    hzeroMu hzeroNu hfirst hsecond hmu hnu
  exact fun n ↦ congrFun hall n

end CompactMeasures

end

end GD.N0232.N0720.N1415

#print axioms _root_.GD.N0232.N0720.N1415.d004087
#print axioms _root_.GD.N0232.N0720.N1415.d004081
#print axioms _root_.GD.N0232.N0720.N1415.d004090
#print axioms _root_.GD.N0232.N0720.N1415.d004093
#print axioms _root_.GD.N0232.N0720.N1415.d004094
