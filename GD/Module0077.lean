






























import Mathlib.Analysis.InnerProductSpace.l2Space
import GD.Module0055

namespace GD
namespace N0230
namespace N0694

open scoped ENNReal RealInnerProductSpace
open _root_.GD.N0230.N0608


noncomputable def d000983 (j : ℤ) : ℝ := (2 : ℝ) ^ (-(j.natAbs : ℤ))

theorem d000984 (j : ℤ) : 0 < _root_.GD.N0230.N0694.d000983 j := zpow_pos two_pos _

theorem d000985 (j : ℤ) : _root_.GD.N0230.N0694.d000983 j ≠ 0 := (_root_.GD.N0230.N0694.d000984 j).ne'

theorem d000986 : _root_.GD.N0230.N0694.d000983 0 = 1 := by simp [_root_.GD.N0230.N0694.d000983]

theorem d000987 (n : ℕ) : _root_.GD.N0230.N0694.d000983 (n : ℤ) = (2 : ℝ)⁻¹ ^ n := by
  simp [_root_.GD.N0230.N0694.d000983, zpow_neg, inv_pow]


theorem d000988 (j : ℤ) : _root_.GD.N0230.N0694.d000983 j ^ 2 = (4 : ℝ)⁻¹ ^ j.natAbs := by
  have h : _root_.GD.N0230.N0694.d000983 j = (2 : ℝ)⁻¹ ^ j.natAbs := by
    rw [_root_.GD.N0230.N0694.d000983, zpow_neg, zpow_natCast, inv_pow]
  rw [h, ← pow_mul, mul_comm, pow_mul]
  norm_num

theorem d000989 : Summable fun j : ℤ => _root_.GD.N0230.N0694.d000983 j ^ 2 := by
  have hgeo : Summable fun n : ℕ => (4 : ℝ)⁻¹ ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have : Summable fun j : ℤ => (4 : ℝ)⁻¹ ^ j.natAbs := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · simpa using hgeo
    · simpa using hgeo
  simpa [_root_.GD.N0230.N0694.d000988] using this


theorem d000990 {f : ∀ _ : ℤ, ℝ}
    (hf : Summable fun j => f j ^ 2) : Memℓp f 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  have hpt : ∀ j : ℤ, ‖f j‖ ^ (2 : ℝ) = f j ^ 2 := by
    intro j
    have : ‖f j‖ ^ (2 : ℝ) = ‖f j‖ ^ (2 : ℕ) := by
      exact_mod_cast Real.rpow_natCast ‖f j‖ 2
    rw [this, Real.norm_eq_abs, sq_abs]
  simpa [hpt] using hf


theorem d000991 (x : lp (fun _ : ℤ => ℝ) 2) :
    Summable fun j : ℤ => x j ^ 2 := by
  have h := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2] at h
  have hpt : ∀ j : ℤ, ‖x j‖ ^ (2 : ℝ) = x j ^ 2 := by
    intro j
    have : ‖x j‖ ^ (2 : ℝ) = ‖x j‖ ^ (2 : ℕ) := by
      exact_mod_cast Real.rpow_natCast ‖x j‖ 2
    rw [this, Real.norm_eq_abs, sq_abs]
  simpa [hpt] using h


noncomputable def d000992 : lp (fun _ : ℤ => ℝ) 2 := ⟨_root_.GD.N0230.N0694.d000983, _root_.GD.N0230.N0694.d000990 _root_.GD.N0230.N0694.d000989⟩

@[simp] theorem d000993 (j : ℤ) : _root_.GD.N0230.N0694.d000992 j = _root_.GD.N0230.N0694.d000983 j := rfl

theorem d000994 : _root_.GD.N0230.N0694.d000992 ≠ 0 := by
  intro h
  have h0 : _root_.GD.N0230.N0694.d000992 0 = (0 : lp (fun _ : ℤ => ℝ) 2) 0 := by rw [h]
  rw [lp.coeFn_zero] at h0
  simp only [_root_.GD.N0230.N0694.d000993, _root_.GD.N0230.N0694.d000986] at h0
  norm_num at h0

theorem d000995 : 0 < ‖_root_.GD.N0230.N0694.d000992‖ := norm_pos_iff.mpr _root_.GD.N0230.N0694.d000994




theorem d000996 (k j : ℤ) : _root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k) ≤ (2 : ℝ) ^ k.natAbs := by
  have hsplit : _root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k) =
      (2 : ℝ) ^ ((((j - k).natAbs : ℤ)) - (j.natAbs : ℤ)) := by
    rw [_root_.GD.N0230.N0694.d000983, _root_.GD.N0230.N0694.d000983, ← zpow_sub₀ (two_ne_zero)]
    ring_nf
  rw [hsplit, ← zpow_natCast (2 : ℝ) k.natAbs]
  apply zpow_le_zpow_right₀ one_le_two
  have htri : (j - k).natAbs ≤ j.natAbs + k.natAbs := Int.natAbs_sub_le j k
  omega

theorem d000997 (k j : ℤ) : 0 < _root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k) :=
  div_pos (_root_.GD.N0230.N0694.d000984 j) (_root_.GD.N0230.N0694.d000984 (j - k))


noncomputable def d000998 (k : ℤ) (x : ∀ _ : ℤ, ℝ) : ∀ _ : ℤ, ℝ :=
  fun j => (_root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k)) * x (j - k)

theorem d000999 (k : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) :
    Memℓp (_root_.GD.N0230.N0694.d000998 k x) 2 := by
  apply _root_.GD.N0230.N0694.d000990
  have hbase : Summable fun j : ℤ => x (j - k) ^ 2 :=
    ((Equiv.subRight k).summable_iff).mpr (_root_.GD.N0230.N0694.d000991 x)
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _)
    (fun j => ?_) (hbase.mul_left ((4 : ℝ) ^ k.natAbs))
  have hexp : (_root_.GD.N0230.N0694.d000998 k x j) ^ 2 = (_root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k)) ^ 2 * x (j - k) ^ 2 := by
    rw [_root_.GD.N0230.N0694.d000998, mul_pow]
  rw [hexp]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h1 : (_root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k)) ^ 2 ≤ ((2 : ℝ) ^ k.natAbs) ^ 2 :=
    pow_le_pow_left₀ (_root_.GD.N0230.N0694.d000997 k j).le (_root_.GD.N0230.N0694.d000996 k j) 2
  calc (_root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k)) ^ 2 ≤ ((2 : ℝ) ^ k.natAbs) ^ 2 := h1
    _ = (4 : ℝ) ^ k.natAbs := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num


noncomputable def d001000 (k : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨_root_.GD.N0230.N0694.d000998 k x, _root_.GD.N0230.N0694.d000999 k x⟩

@[simp] theorem d001001 (k : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    _root_.GD.N0230.N0694.d001000 k x j = (_root_.GD.N0230.N0694.d000983 j / _root_.GD.N0230.N0694.d000983 (j - k)) * x (j - k) := rfl

theorem d001002 (x : lp (fun _ : ℤ => ℝ) 2) : _root_.GD.N0230.N0694.d001000 0 x = x := by
  apply lp.ext
  funext j
  simp [div_self (_root_.GD.N0230.N0694.d000985 j)]


theorem d001003 (k l : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) :
    _root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d001000 l x) = _root_.GD.N0230.N0694.d001000 (k + l) x := by
  apply lp.ext
  funext j
  have hidx : j - k - l = j - (k + l) := by ring
  simp only [_root_.GD.N0230.N0694.d001001, hidx]
  have h1 := _root_.GD.N0230.N0694.d000985 (j - k)
  have h2 := _root_.GD.N0230.N0694.d000985 (j - (k + l))
  field_simp

theorem d001004 (k : ℤ) (x y : lp (fun _ : ℤ => ℝ) 2) :
    _root_.GD.N0230.N0694.d001000 k (x + y) = _root_.GD.N0230.N0694.d001000 k x + _root_.GD.N0230.N0694.d001000 k y := by
  apply lp.ext
  funext j
  simp only [lp.coeFn_add, Pi.add_apply, _root_.GD.N0230.N0694.d001001]
  ring

theorem d001005 (k : ℤ) (c : ℝ) (x : lp (fun _ : ℤ => ℝ) 2) :
    _root_.GD.N0230.N0694.d001000 k (c • x) = c • _root_.GD.N0230.N0694.d001000 k x := by
  apply lp.ext
  funext j
  simp only [lp.coeFn_smul, Pi.smul_apply, _root_.GD.N0230.N0694.d001001, smul_eq_mul]
  ring


theorem d001006 (k : ℤ) : _root_.GD.N0230.N0694.d001000 k _root_.GD.N0230.N0694.d000992 = _root_.GD.N0230.N0694.d000992 := by
  apply lp.ext
  funext j
  simp only [_root_.GD.N0230.N0694.d001001, _root_.GD.N0230.N0694.d000993]
  exact div_mul_cancel₀ (_root_.GD.N0230.N0694.d000983 j) (_root_.GD.N0230.N0694.d000985 (j - k))


theorem d001007 (x : lp (fun _ : ℤ => ℝ) 2) :
    (∀ k, _root_.GD.N0230.N0694.d001000 k x = x) ↔ ∃ c : ℝ, x = c • _root_.GD.N0230.N0694.d000992 := by
  constructor
  · intro h
    refine ⟨x 0, ?_⟩
    apply lp.ext
    funext j
    have hj : _root_.GD.N0230.N0694.d001000 j x j = x j := by rw [h j]
    simp only [_root_.GD.N0230.N0694.d001001, sub_self, _root_.GD.N0230.N0694.d000986, div_one] at hj
    simp only [lp.coeFn_smul, Pi.smul_apply, _root_.GD.N0230.N0694.d000993, smul_eq_mul]
    rw [← hj]; ring
  · rintro ⟨c, rfl⟩ k
    rw [_root_.GD.N0230.N0694.d001005, _root_.GD.N0230.N0694.d001006]




noncomputable def d001008 : lp (fun _ : ℤ => ℝ) 2 := lp.single 2 0 1

theorem d001009 : _root_.GD.N0230.N0694.d001008 ≠ 0 := by
  intro h
  have h0 : _root_.GD.N0230.N0694.d001008 0 = (0 : lp (fun _ : ℤ => ℝ) 2) 0 := by rw [h]
  rw [lp.coeFn_zero] at h0
  simp [_root_.GD.N0230.N0694.d001008, lp.single_apply] at h0

theorem d001010 (k i : ℤ) (a : ℝ) :
    _root_.GD.N0230.N0694.d001000 k (lp.single 2 i a) = lp.single 2 (i + k) (_root_.GD.N0230.N0694.d000983 (i + k) / _root_.GD.N0230.N0694.d000983 i * a) := by
  apply lp.ext
  funext j
  simp only [_root_.GD.N0230.N0694.d001001, lp.single_apply]
  by_cases h : j = i + k
  · subst h
    have h1 : i + k - k = i := by ring
    rw [h1, Pi.single_eq_same, Pi.single_eq_same]
  · have h1 : j - k ≠ i := fun hc => h (by omega)
    rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h, mul_zero]


theorem d001011 (k : ℤ) : _root_.GD.N0230.N0694.d001000 k _root_.GD.N0230.N0694.d001008 = lp.single 2 k (_root_.GD.N0230.N0694.d000983 k) := by
  show _root_.GD.N0230.N0694.d001000 k (lp.single 2 0 1) = lp.single 2 k (_root_.GD.N0230.N0694.d000983 k)
  rw [_root_.GD.N0230.N0694.d001010, zero_add, _root_.GD.N0230.N0694.d000986, div_one, mul_one]

theorem d001012 (i : ℤ) (a : ℝ) :
    ‖lp.single (E := fun _ : ℤ => ℝ) 2 i a‖ = |a| := by
  rw [lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]
  exact Real.norm_eq_abs a

theorem d001013 (i : ℤ) (a : ℝ) :
    ⟪lp.single (E := fun _ : ℤ => ℝ) 2 i a, _root_.GD.N0230.N0694.d000992⟫ = a * _root_.GD.N0230.N0694.d000983 i := by
  rw [lp.inner_single_left]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, _root_.GD.N0230.N0694.d000993]
  ring




noncomputable def d001014 (k : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) : ℝ≥0∞ :=
  ENNReal.ofReal (‖_root_.GD.N0230.N0694.d001000 (-k) x - (2 : ℝ) • _root_.GD.N0230.N0694.d000992‖ ^ 2)


noncomputable def d001015 (k : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) : ℝ≥0∞ :=
  ENNReal.ofReal (‖_root_.GD.N0230.N0694.d001000 (-k) x‖ ^ 2)


noncomputable def d001016 : ℤ ⊕ ℤ → lp (fun _ : ℤ => ℝ) 2 → ℝ≥0∞ :=
  Sum.elim _root_.GD.N0230.N0694.d001014 _root_.GD.N0230.N0694.d001015


theorem d001017 (k l : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) :
    _root_.GD.N0230.N0694.d001014 k (_root_.GD.N0230.N0694.d001000 l x) = _root_.GD.N0230.N0694.d001014 (k - l) x := by
  rw [_root_.GD.N0230.N0694.d001014, _root_.GD.N0230.N0694.d001014, _root_.GD.N0230.N0694.d001003]
  congr 2
  ring

theorem d001018 (k l : ℤ) (x : lp (fun _ : ℤ => ℝ) 2) :
    _root_.GD.N0230.N0694.d001015 k (_root_.GD.N0230.N0694.d001000 l x) = _root_.GD.N0230.N0694.d001015 (k - l) x := by
  rw [_root_.GD.N0230.N0694.d001015, _root_.GD.N0230.N0694.d001015, _root_.GD.N0230.N0694.d001003]
  congr 3
  ring

theorem d001019 (k : ℤ) : _root_.GD.N0230.N0694.d001014 k _root_.GD.N0230.N0694.d000992 = ENNReal.ofReal (‖_root_.GD.N0230.N0694.d000992‖ ^ 2) := by
  rw [_root_.GD.N0230.N0694.d001014, _root_.GD.N0230.N0694.d001006]
  congr 2
  have h : _root_.GD.N0230.N0694.d000992 - (2 : ℝ) • _root_.GD.N0230.N0694.d000992 = -_root_.GD.N0230.N0694.d000992 := by
    rw [two_smul]; abel
  rw [h, norm_neg]

theorem d001020 (k : ℤ) (c : ℝ) :
    _root_.GD.N0230.N0694.d001014 k (c • _root_.GD.N0230.N0694.d000992) = ENNReal.ofReal ((c - 2) ^ 2 * ‖_root_.GD.N0230.N0694.d000992‖ ^ 2) := by
  rw [_root_.GD.N0230.N0694.d001014, _root_.GD.N0230.N0694.d001005, _root_.GD.N0230.N0694.d001006]
  congr 1
  have h : c • _root_.GD.N0230.N0694.d000992 - (2 : ℝ) • _root_.GD.N0230.N0694.d000992 = (c - 2) • _root_.GD.N0230.N0694.d000992 := by
    rw [sub_smul]
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem d001021 (k : ℤ) : _root_.GD.N0230.N0694.d001015 k _root_.GD.N0230.N0694.d000992 = ENNReal.ofReal (‖_root_.GD.N0230.N0694.d000992‖ ^ 2) := by
  rw [_root_.GD.N0230.N0694.d001015, _root_.GD.N0230.N0694.d001006]


theorem d001022 : _root_.GD.N0230.N0608.d000672 _root_.GD.N0230.N0694.d001014 _root_.GD.N0230.N0694.d000992 ((3 : ℝ) • _root_.GD.N0230.N0694.d000992) := by
  intro k
  rw [_root_.GD.N0230.N0694.d001019, _root_.GD.N0230.N0694.d001020]
  norm_num


theorem d001023 (x : lp (fun _ : ℤ => ℝ) 2)
    (hfix : ∀ k, _root_.GD.N0230.N0694.d001000 k x = x)
    (hcone : _root_.GD.N0230.N0608.d000672 _root_.GD.N0230.N0694.d001014 x ((3 : ℝ) • _root_.GD.N0230.N0694.d000992)) : ‖_root_.GD.N0230.N0694.d000992‖ ≤ ‖x‖ := by
  obtain ⟨c, rfl⟩ := (_root_.GD.N0230.N0694.d001007 x).mp hfix
  have h0 := hcone 0
  rw [_root_.GD.N0230.N0694.d001020, _root_.GD.N0230.N0694.d001020] at h0
  have hreal : (c - 2) ^ 2 * ‖_root_.GD.N0230.N0694.d000992‖ ^ 2 ≤ (3 - 2 : ℝ) ^ 2 * ‖_root_.GD.N0230.N0694.d000992‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h0
  have hsq : (c - 2) ^ 2 ≤ 1 := by
    have hpos : (0 : ℝ) < ‖_root_.GD.N0230.N0694.d000992‖ ^ 2 := pow_pos _root_.GD.N0230.N0694.d000995 2
    nlinarith
  have hc : 1 ≤ c := by nlinarith [sq_nonneg (c - 1)]
  rw [norm_smul, Real.norm_eq_abs]
  have : 1 * ‖_root_.GD.N0230.N0694.d000992‖ ≤ |c| * ‖_root_.GD.N0230.N0694.d000992‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [abs_of_pos (by linarith : (0 : ℝ) < c)]
    exact hc
  linarith



theorem d001024 (k : ℤ) :
    _root_.GD.N0230.N0694.d001014 k (_root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) = ENNReal.ofReal (‖_root_.GD.N0230.N0694.d000992‖ ^ 2 - _root_.GD.N0230.N0694.d000983 (-k) ^ 2) := by
  rw [_root_.GD.N0230.N0694.d001014, _root_.GD.N0230.N0694.d001004, _root_.GD.N0230.N0694.d001006, _root_.GD.N0230.N0694.d001011]
  congr 1
  have hre : _root_.GD.N0230.N0694.d000992 + lp.single 2 (-k) (_root_.GD.N0230.N0694.d000983 (-k)) - (2 : ℝ) • _root_.GD.N0230.N0694.d000992 =
      lp.single 2 (-k) (_root_.GD.N0230.N0694.d000983 (-k)) - _root_.GD.N0230.N0694.d000992 := by
    rw [two_smul]; abel
  rw [hre, norm_sub_sq_real, _root_.GD.N0230.N0694.d001013, _root_.GD.N0230.N0694.d001012,
    abs_of_pos (_root_.GD.N0230.N0694.d000984 (-k))]
  ring



theorem d001025 :
    _root_.GD.N0230.N0608.d000675 _root_.GD.N0230.N0694.d001014 (_root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) _root_.GD.N0230.N0694.d000992 := by
  intro k
  rw [_root_.GD.N0230.N0694.d001024, _root_.GD.N0230.N0694.d001019]
  apply (ENNReal.ofReal_lt_ofReal_iff (pow_pos _root_.GD.N0230.N0694.d000995 2)).mpr
  have hw := pow_pos (_root_.GD.N0230.N0694.d000984 (-k)) 2
  linarith

theorem d001026 : _root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008 ≠ _root_.GD.N0230.N0694.d000992 := by
  intro h
  exact _root_.GD.N0230.N0694.d001009 (by simpa using congrArg (fun z => z - _root_.GD.N0230.N0694.d000992) h)


theorem d001027 : ¬ (∀ k, _root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) = _root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) := by
  intro h
  obtain ⟨c, hc⟩ := (_root_.GD.N0230.N0694.d001007 _).mp h
  have key : ∀ j : ℤ, _root_.GD.N0230.N0694.d000983 j + (Pi.single 0 (1 : ℝ) : ∀ _ : ℤ, ℝ) j = c * _root_.GD.N0230.N0694.d000983 j := by
    intro j
    have hj := congrArg (fun z : lp (fun _ : ℤ => ℝ) 2 => (z : ∀ _ : ℤ, ℝ) j) hc
    simpa [lp.coeFn_add, lp.coeFn_smul, _root_.GD.N0230.N0694.d001008, lp.single_apply, Pi.smul_apply,
      smul_eq_mul] using hj
  have k0 := key 0
  have k1 := key 1
  rw [Pi.single_eq_same, _root_.GD.N0230.N0694.d000986] at k0
  rw [Pi.single_eq_of_ne (by norm_num : (1 : ℤ) ≠ 0)] at k1
  have hc2 : c = 2 := by linarith
  have hw1 : _root_.GD.N0230.N0694.d000983 1 ≠ 0 := _root_.GD.N0230.N0694.d000985 1
  have h1' : (1 : ℝ) * _root_.GD.N0230.N0694.d000983 1 = c * _root_.GD.N0230.N0694.d000983 1 := by linarith
  have : (1 : ℝ) = c := mul_right_cancel₀ hw1 h1'
  linarith




theorem d001028 : ¬ _root_.GD.N0230.N0608.d000674 _root_.GD.N0230.N0694.d001014 _root_.GD.N0230.N0694.d000992 := by
  intro h
  exact _root_.GD.N0230.N0694.d001026
    (h (_root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) (fun k => (_root_.GD.N0230.N0694.d001025 k).le))



theorem d001029 (k : ℤ) :
    ‖_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) - _root_.GD.N0230.N0694.d000992‖ = _root_.GD.N0230.N0694.d000983 k := by
  rw [_root_.GD.N0230.N0694.d001004, _root_.GD.N0230.N0694.d001006, _root_.GD.N0230.N0694.d001011]
  have h : _root_.GD.N0230.N0694.d000992 + lp.single 2 k (_root_.GD.N0230.N0694.d000983 k) - _root_.GD.N0230.N0694.d000992 = lp.single 2 k (_root_.GD.N0230.N0694.d000983 k) := by abel
  rw [h, _root_.GD.N0230.N0694.d001012, abs_of_pos (_root_.GD.N0230.N0694.d000984 k)]




theorem d001030 :
    Filter.Tendsto (fun n : ℕ => ‖_root_.GD.N0230.N0694.d001000 n (_root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) - _root_.GD.N0230.N0694.d000992‖)
      Filter.atTop (nhds 0) := by
  have hpt : (fun n : ℕ => ‖_root_.GD.N0230.N0694.d001000 n (_root_.GD.N0230.N0694.d000992 + _root_.GD.N0230.N0694.d001008) - _root_.GD.N0230.N0694.d000992‖) =
      fun n : ℕ => (2 : ℝ)⁻¹ ^ n := by
    funext n
    rw [_root_.GD.N0230.N0694.d001029, _root_.GD.N0230.N0694.d000987]
  rw [hpt]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)




theorem d001031 : _root_.GD.N0230.N0608.d000672 _root_.GD.N0230.N0694.d001016 _root_.GD.N0230.N0694.d000992 ((3 : ℝ) • _root_.GD.N0230.N0694.d000992) := by
  rintro (k | k)
  · exact _root_.GD.N0230.N0694.d001022 k
  · show _root_.GD.N0230.N0694.d001015 k _root_.GD.N0230.N0694.d000992 ≤ _root_.GD.N0230.N0694.d001015 k ((3 : ℝ) • _root_.GD.N0230.N0694.d000992)
    rw [_root_.GD.N0230.N0694.d001015, _root_.GD.N0230.N0694.d001015, _root_.GD.N0230.N0694.d001006, _root_.GD.N0230.N0694.d001005, _root_.GD.N0230.N0694.d001006, norm_smul]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg ‖_root_.GD.N0230.N0694.d000992‖, norm_nonneg _root_.GD.N0230.N0694.d000992]


theorem d001032 (x : lp (fun _ : ℤ => ℝ) 2)
    (hfix : ∀ k, _root_.GD.N0230.N0694.d001000 k x = x)
    (hcone : _root_.GD.N0230.N0608.d000672 _root_.GD.N0230.N0694.d001016 x ((3 : ℝ) • _root_.GD.N0230.N0694.d000992)) : ‖_root_.GD.N0230.N0694.d000992‖ ≤ ‖x‖ :=
  _root_.GD.N0230.N0694.d001023 x hfix (fun k => hcone (Sum.inl k))




theorem d001033 : _root_.GD.N0230.N0608.d000674 _root_.GD.N0230.N0694.d001016 _root_.GD.N0230.N0694.d000992 := by
  intro e he
  have hA := he (Sum.inl 0)
  have hB := he (Sum.inr 0)
  have hz : (-(0:ℤ)) = 0 := by norm_num
  rw [show _root_.GD.N0230.N0694.d001016 (Sum.inl 0) = _root_.GD.N0230.N0694.d001014 0 from rfl] at hA
  rw [show _root_.GD.N0230.N0694.d001016 (Sum.inr 0) = _root_.GD.N0230.N0694.d001015 0 from rfl] at hB
  rw [_root_.GD.N0230.N0694.d001019, _root_.GD.N0230.N0694.d001014, hz, _root_.GD.N0230.N0694.d001002] at hA
  rw [_root_.GD.N0230.N0694.d001021, _root_.GD.N0230.N0694.d001015, hz, _root_.GD.N0230.N0694.d001002] at hB
  have hAr : ‖e - (2:ℝ) • _root_.GD.N0230.N0694.d000992‖ ^ 2 ≤ ‖_root_.GD.N0230.N0694.d000992‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hA
  have hBr : ‖e‖ ^ 2 ≤ ‖_root_.GD.N0230.N0694.d000992‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hB
  set v := e - _root_.GD.N0230.N0694.d000992 with hv
  have hrw1 : e - (2:ℝ) • _root_.GD.N0230.N0694.d000992 = v - _root_.GD.N0230.N0694.d000992 := by
    rw [hv, two_smul]; abel
  have hrw2 : e = v + _root_.GD.N0230.N0694.d000992 := by rw [hv]; abel
  rw [hrw1, norm_sub_sq_real] at hAr
  rw [hrw2, norm_add_sq_real] at hBr
  have hvz : ‖v‖ ^ 2 ≤ 0 := by linarith
  have : v = 0 := by
    have h0 : ‖v‖ ^ 2 = 0 := le_antisymm hvz (by positivity)
    have : ‖v‖ = 0 := by
      nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp this
  have : e - _root_.GD.N0230.N0694.d000992 = 0 := this
  exact sub_eq_zero.mp this



#print axioms _root_.GD.N0230.N0694.d001025
#print axioms _root_.GD.N0230.N0694.d001028
#print axioms _root_.GD.N0230.N0694.d001023
#print axioms _root_.GD.N0230.N0694.d001022
#print axioms _root_.GD.N0230.N0694.d001027
#print axioms _root_.GD.N0230.N0694.d001030
#print axioms _root_.GD.N0230.N0694.d001033
#print axioms _root_.GD.N0230.N0694.d001032
#print axioms _root_.GD.N0230.N0694.d001017
#print axioms _root_.GD.N0230.N0694.d001007

end N0694
end N0230
end GD
