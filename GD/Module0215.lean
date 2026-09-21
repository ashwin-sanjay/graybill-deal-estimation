import Mathlib



















namespace GD
namespace N0232
namespace N0720
namespace N1410

noncomputable section

def d002957 (e : ℝ) : ℝ := 1 - e
def d002958 (e : ℝ) : ℝ := 1 - 2 * e
def d002959 (e : ℝ) : ℝ := 1 - 2 * e + 2 * e ^ 2

def d002960 (e : ℝ) : ℝ :=
  1 + (3 / 2 : ℝ) * e ^ 2 + 3 * e ^ 3 + (17 / 2 : ℝ) * e ^ 4

def d002961 (e : ℝ) : ℝ :=
  1 - 4 * e + (11 / 2 : ℝ) * e ^ 2 - 3 * e ^ 3 + (3 / 8 : ℝ) * e ^ 4

def d002962 (e : ℝ) : ℝ :=
  2 - 4 * e - 3 * e ^ 2 + (17 / 2 : ℝ) * e ^ 4

def d002963 (e : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1410.d002957 e ^ 3 / (_root_.GD.N0232.N0720.N1410.d002958 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e))

def d002964 (e : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1410.d002957 e ^ 3 * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e)

def d002965 (e : ℝ) : ℝ :=
  2 * _root_.GD.N0232.N0720.N1410.d002958 e * _root_.GD.N0232.N0720.N1410.d002957 e ^ 3 /
    (_root_.GD.N0232.N0720.N1410.d002959 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002959 e))



def d002966 (e : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1410.d002963 e + _root_.GD.N0232.N0720.N1410.d002964 e + _root_.GD.N0232.N0720.N1410.d002965 e - 4 * _root_.GD.N0232.N0720.N1410.d002957 e ^ 2

private theorem d002967
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    0 ≤ 1 / 9 - e ∧ 0 < _root_.GD.N0232.N0720.N1410.d002957 e ∧ 0 < _root_.GD.N0232.N0720.N1410.d002958 e ∧ 0 < _root_.GD.N0232.N0720.N1410.d002959 e := by
  have hs1 : 0 < _root_.GD.N0232.N0720.N1410.d002957 e := by
    unfold _root_.GD.N0232.N0720.N1410.d002957
    linarith
  have hs2 : 0 < _root_.GD.N0232.N0720.N1410.d002958 e := by
    unfold _root_.GD.N0232.N0720.N1410.d002958
    linarith
  have hmixed : 0 < _root_.GD.N0232.N0720.N1410.d002959 e := by
    unfold _root_.GD.N0232.N0720.N1410.d002959
    nlinarith [sq_nonneg (e - 1 / 2)]
  exact ⟨sub_nonneg.mpr he9, hs1, hs2, hmixed⟩

private theorem d002968 (e : ℝ) :
    _root_.GD.N0232.N0720.N1410.d002960 e ^ 2 * _root_.GD.N0232.N0720.N1410.d002958 e ^ 3 - _root_.GD.N0232.N0720.N1410.d002957 e ^ 6 =
      e ^ 4 *
        (578 * (1 / 9 - e) ^ 7 +
          (85 / 9 : ℝ) * (1 / 9 - e) ^ 6 -
          (3167 / 54 : ℝ) * (1 / 9 - e) ^ 5 +
          (324647 / 2916 : ℝ) * (1 / 9 - e) ^ 4 +
          (1026250 / 6561 : ℝ) * (1 / 9 - e) ^ 3 +
          (2021278 / 19683 : ℝ) * (1 / 9 - e) ^ 2 +
          (12388784 / 531441 : ℝ) * (1 / 9 - e) +
          (771676 / 4782969 : ℝ)) := by
  unfold _root_.GD.N0232.N0720.N1410.d002960 _root_.GD.N0232.N0720.N1410.d002957 _root_.GD.N0232.N0720.N1410.d002958
  ring

private theorem d002969
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    0 ≤ _root_.GD.N0232.N0720.N1410.d002960 e ^ 2 * _root_.GD.N0232.N0720.N1410.d002958 e ^ 3 - _root_.GD.N0232.N0720.N1410.d002957 e ^ 6 := by
  let t : ℝ := 1 / 9 - e
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht9 : t ≤ 1 / 9 := by dsimp [t]; linarith
  have hcoef :
      0 ≤ (324647 / 2916 : ℝ) - (3167 / 54 : ℝ) * t := by
    linarith
  have hgroup :
      0 ≤ (324647 / 2916 : ℝ) * t ^ 4 -
        (3167 / 54 : ℝ) * t ^ 5 := by
    have h := mul_nonneg (pow_nonneg ht0 4) hcoef
    nlinarith
  have hpoly :
      0 ≤ 578 * t ^ 7 + (85 / 9 : ℝ) * t ^ 6 -
          (3167 / 54 : ℝ) * t ^ 5 +
          (324647 / 2916 : ℝ) * t ^ 4 +
          (1026250 / 6561 : ℝ) * t ^ 3 +
          (2021278 / 19683 : ℝ) * t ^ 2 +
          (12388784 / 531441 : ℝ) * t +
          (771676 / 4782969 : ℝ) := by
    have h7 : 0 ≤ 578 * t ^ 7 := mul_nonneg (by norm_num) (pow_nonneg ht0 7)
    have h6 : 0 ≤ (85 / 9 : ℝ) * t ^ 6 :=
      mul_nonneg (by norm_num) (pow_nonneg ht0 6)
    have h3 : 0 ≤ (1026250 / 6561 : ℝ) * t ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg ht0 3)
    have h2 : 0 ≤ (2021278 / 19683 : ℝ) * t ^ 2 :=
      mul_nonneg (by norm_num) (pow_nonneg ht0 2)
    have h1 : 0 ≤ (12388784 / 531441 : ℝ) * t :=
      mul_nonneg (by norm_num) ht0
    nlinarith
  rw [_root_.GD.N0232.N0720.N1410.d002968]
  dsimp [t] at hpoly
  exact mul_nonneg (pow_nonneg he0 4) hpoly

theorem d002970
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    _root_.GD.N0232.N0720.N1410.d002963 e ≤ _root_.GD.N0232.N0720.N1410.d002960 e := by
  obtain ⟨_, hs1, hs2, _⟩ := _root_.GD.N0232.N0720.N1410.d002967 he0 he9
  have hsqrt : 0 < Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e) := Real.sqrt_pos.2 hs2
  have hsqrtSq : Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e) ^ 2 = _root_.GD.N0232.N0720.N1410.d002958 e :=
    Real.sq_sqrt hs2.le
  have hupper : 0 ≤ _root_.GD.N0232.N0720.N1410.d002960 e := by
    unfold _root_.GD.N0232.N0720.N1410.d002960
    positivity
  have hleft : 0 ≤ _root_.GD.N0232.N0720.N1410.d002957 e ^ 3 := pow_nonneg hs1.le 3
  have hright : 0 ≤ _root_.GD.N0232.N0720.N1410.d002960 e * (_root_.GD.N0232.N0720.N1410.d002958 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e)) :=
    mul_nonneg hupper (mul_nonneg hs2.le hsqrt.le)
  have hsquares :
      (_root_.GD.N0232.N0720.N1410.d002957 e ^ 3) ^ 2 ≤
        (_root_.GD.N0232.N0720.N1410.d002960 e * (_root_.GD.N0232.N0720.N1410.d002958 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e))) ^ 2 := by
    have hcert := _root_.GD.N0232.N0720.N1410.d002969 he0 he9
    nlinarith
  have hroot :
      _root_.GD.N0232.N0720.N1410.d002957 e ^ 3 ≤ _root_.GD.N0232.N0720.N1410.d002960 e * (_root_.GD.N0232.N0720.N1410.d002958 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e)) := by
    nlinarith
  unfold _root_.GD.N0232.N0720.N1410.d002963
  exact (div_le_iff₀ (mul_pos hs2 hsqrt)).2 (by simpa [mul_assoc] using hroot)

private theorem d002971 (e : ℝ) :
    _root_.GD.N0232.N0720.N1410.d002961 e ^ 2 - _root_.GD.N0232.N0720.N1410.d002957 e ^ 6 * _root_.GD.N0232.N0720.N1410.d002958 e =
      e ^ 6 * (9 * e ^ 2 - 16 * e + 8) / 64 := by
  unfold _root_.GD.N0232.N0720.N1410.d002961 _root_.GD.N0232.N0720.N1410.d002957 _root_.GD.N0232.N0720.N1410.d002958
  ring

theorem d002972
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    _root_.GD.N0232.N0720.N1410.d002964 e ≤ _root_.GD.N0232.N0720.N1410.d002961 e := by
  obtain ⟨_, hs1, hs2, _⟩ := _root_.GD.N0232.N0720.N1410.d002967 he0 he9
  have hsqrt0 : 0 ≤ Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (_root_.GD.N0232.N0720.N1410.d002958 e) ^ 2 = _root_.GD.N0232.N0720.N1410.d002958 e :=
    Real.sq_sqrt hs2.le
  have hupper : 0 ≤ _root_.GD.N0232.N0720.N1410.d002961 e := by
    have hcore : 0 ≤ (11 / 2 : ℝ) - 3 * e := by linarith
    have htail : 0 ≤ e ^ 2 * ((11 / 2 : ℝ) - 3 * e) :=
      mul_nonneg (pow_nonneg he0 2) hcore
    unfold _root_.GD.N0232.N0720.N1410.d002961
    nlinarith [pow_nonneg he0 4]
  have hfactor : 0 ≤ 9 * e ^ 2 - 16 * e + 8 := by
    nlinarith [sq_nonneg e]
  have hcert : 0 ≤ _root_.GD.N0232.N0720.N1410.d002961 e ^ 2 - _root_.GD.N0232.N0720.N1410.d002957 e ^ 6 * _root_.GD.N0232.N0720.N1410.d002958 e := by
    rw [_root_.GD.N0232.N0720.N1410.d002971]
    positivity
  have hleft : 0 ≤ _root_.GD.N0232.N0720.N1410.d002964 e := by
    unfold _root_.GD.N0232.N0720.N1410.d002964
    positivity
  have hsquares : _root_.GD.N0232.N0720.N1410.d002964 e ^ 2 ≤ _root_.GD.N0232.N0720.N1410.d002961 e ^ 2 := by
    unfold _root_.GD.N0232.N0720.N1410.d002964
    nlinarith
  nlinarith

private theorem d002973 (e : ℝ) :
    _root_.GD.N0232.N0720.N1410.d002962 e ^ 2 * _root_.GD.N0232.N0720.N1410.d002959 e ^ 3 -
        4 * _root_.GD.N0232.N0720.N1410.d002958 e ^ 2 * _root_.GD.N0232.N0720.N1410.d002957 e ^ 6 =
      e ^ 4 *
        (578 * (1 / 9 - e) ^ 10 +
          (9826 / 9 : ℝ) * (1 / 9 - e) ^ 9 +
          (7021 / 9 : ℝ) * (1 / 9 - e) ^ 8 +
          (87040 / 243 : ℝ) * (1 / 9 - e) ^ 7 +
          (3271483 / 4374 : ℝ) * (1 / 9 - e) ^ 6 +
          (18563045 / 13122 : ℝ) * (1 / 9 - e) ^ 5 +
          (967752443 / 708588 : ℝ) * (1 / 9 - e) ^ 4 +
          (1175008942 / 1594323 : ℝ) * (1 / 9 - e) ^ 3 +
          (1027743769 / 4782969 : ℝ) * (1 / 9 - e) ^ 2 +
          (20377977431 / 774840978 : ℝ) * (1 / 9 - e) +
          (2516765489 / 13947137604 : ℝ)) := by
  unfold _root_.GD.N0232.N0720.N1410.d002962 _root_.GD.N0232.N0720.N1410.d002959 _root_.GD.N0232.N0720.N1410.d002957 _root_.GD.N0232.N0720.N1410.d002958
  ring

private theorem d002974
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    0 ≤ _root_.GD.N0232.N0720.N1410.d002962 e ^ 2 * _root_.GD.N0232.N0720.N1410.d002959 e ^ 3 -
      4 * _root_.GD.N0232.N0720.N1410.d002958 e ^ 2 * _root_.GD.N0232.N0720.N1410.d002957 e ^ 6 := by
  rw [_root_.GD.N0232.N0720.N1410.d002973]
  have ht : 0 ≤ 1 / 9 - e := sub_nonneg.mpr he9
  have hpoly :
      0 ≤ 578 * (1 / 9 - e) ^ 10 +
          (9826 / 9 : ℝ) * (1 / 9 - e) ^ 9 +
          (7021 / 9 : ℝ) * (1 / 9 - e) ^ 8 +
          (87040 / 243 : ℝ) * (1 / 9 - e) ^ 7 +
          (3271483 / 4374 : ℝ) * (1 / 9 - e) ^ 6 +
          (18563045 / 13122 : ℝ) * (1 / 9 - e) ^ 5 +
          (967752443 / 708588 : ℝ) * (1 / 9 - e) ^ 4 +
          (1175008942 / 1594323 : ℝ) * (1 / 9 - e) ^ 3 +
          (1027743769 / 4782969 : ℝ) * (1 / 9 - e) ^ 2 +
          (20377977431 / 774840978 : ℝ) * (1 / 9 - e) +
          (2516765489 / 13947137604 : ℝ) := by
    positivity
  exact mul_nonneg (pow_nonneg he0 4) hpoly

theorem d002975
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    _root_.GD.N0232.N0720.N1410.d002965 e ≤ _root_.GD.N0232.N0720.N1410.d002962 e := by
  obtain ⟨_, hs1, hs2, hmixed⟩ := _root_.GD.N0232.N0720.N1410.d002967 he0 he9
  have hsqrt : 0 < Real.sqrt (_root_.GD.N0232.N0720.N1410.d002959 e) := Real.sqrt_pos.2 hmixed
  have hsqrtSq : Real.sqrt (_root_.GD.N0232.N0720.N1410.d002959 e) ^ 2 = _root_.GD.N0232.N0720.N1410.d002959 e :=
    Real.sq_sqrt hmixed.le
  have hupper : 0 ≤ _root_.GD.N0232.N0720.N1410.d002962 e := by
    have heSq : e ^ 2 ≤ (1 / 9 : ℝ) ^ 2 := by nlinarith
    unfold _root_.GD.N0232.N0720.N1410.d002962
    nlinarith [pow_nonneg he0 4]
  have hleft : 0 ≤ 2 * _root_.GD.N0232.N0720.N1410.d002958 e * _root_.GD.N0232.N0720.N1410.d002957 e ^ 3 := by positivity
  have hright :
      0 ≤ _root_.GD.N0232.N0720.N1410.d002962 e * (_root_.GD.N0232.N0720.N1410.d002959 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002959 e)) := by
    positivity
  have hsquares :
      (2 * _root_.GD.N0232.N0720.N1410.d002958 e * _root_.GD.N0232.N0720.N1410.d002957 e ^ 3) ^ 2 ≤
        (_root_.GD.N0232.N0720.N1410.d002962 e *
          (_root_.GD.N0232.N0720.N1410.d002959 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002959 e))) ^ 2 := by
    have hcert := _root_.GD.N0232.N0720.N1410.d002974 he0 he9
    nlinarith
  have hroot :
      2 * _root_.GD.N0232.N0720.N1410.d002958 e * _root_.GD.N0232.N0720.N1410.d002957 e ^ 3 ≤
        _root_.GD.N0232.N0720.N1410.d002962 e * (_root_.GD.N0232.N0720.N1410.d002959 e * Real.sqrt (_root_.GD.N0232.N0720.N1410.d002959 e)) := by
    nlinarith
  unfold _root_.GD.N0232.N0720.N1410.d002965
  exact (div_le_iff₀ (mul_pos hmixed hsqrt)).2 (by
    simpa [mul_assoc] using hroot)




theorem d002976
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    _root_.GD.N0232.N0720.N1410.d002966 e ≤ 18 * e ^ 4 := by
  have hA := _root_.GD.N0232.N0720.N1410.d002970 he0 he9
  have hB := _root_.GD.N0232.N0720.N1410.d002972 he0 he9
  have hC := _root_.GD.N0232.N0720.N1410.d002975 he0 he9
  unfold _root_.GD.N0232.N0720.N1410.d002966
  have hsum :
      _root_.GD.N0232.N0720.N1410.d002960 e + _root_.GD.N0232.N0720.N1410.d002961 e + _root_.GD.N0232.N0720.N1410.d002962 e - 4 * _root_.GD.N0232.N0720.N1410.d002957 e ^ 2 =
        (139 / 8 : ℝ) * e ^ 4 := by
    unfold _root_.GD.N0232.N0720.N1410.d002960 _root_.GD.N0232.N0720.N1410.d002961 _root_.GD.N0232.N0720.N1410.d002962 _root_.GD.N0232.N0720.N1410.d002957
    ring
  have he4 : 0 ≤ e ^ 4 := by positivity
  linarith

end

end N1410
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1410.d002970
#print axioms _root_.GD.N0232.N0720.N1410.d002972
#print axioms _root_.GD.N0232.N0720.N1410.d002975
#print axioms _root_.GD.N0232.N0720.N1410.d002976
