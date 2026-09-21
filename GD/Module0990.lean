import GD.Module0972











open MeasureTheory

namespace GD.N0232.N0720.N1465

noncomputable section

open _root_.GD.N0141
open _root_.GD.N0120
open _root_.GD.N0145
open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0108
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1085
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

noncomputable local instance d015693 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance


def d015694 (lambda : ℝ) : ℝ :=
  5 / 4 + (1 - lambda) / 2

theorem d015695
    {lambda : ℝ} (hlambda : lambda < 1) :
    (5 / 4 : ℝ) < _root_.GD.N0232.N0720.N1465.d015694 lambda := by
  unfold _root_.GD.N0232.N0720.N1465.d015694
  linarith


theorem d015696
    {fullGap energy gap lambda : ℝ}
    (hfull : fullGap ≤ -(3 / 2 : ℝ) * gap)
    (henergy : energy ≤ lambda * gap)
    (hgap : 0 < gap) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda < 1) :
    (_root_.GD.N0232.N0720.N1465.d015694 lambda - 5 / 4) *
        (fullGap + (_root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1) * energy) < 0 := by
  have hcoef : 0 ≤ _root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1 := by
    unfold _root_.GD.N0232.N0720.N1465.d015694
    linarith
  have hba : 0 < _root_.GD.N0232.N0720.N1465.d015694 lambda - 5 / 4 := by
    exact sub_pos.mpr (_root_.GD.N0232.N0720.N1465.d015695 hlambda1)
  have hterm :
      (_root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1) * energy ≤
        (_root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1) * (lambda * gap) :=
    mul_le_mul_of_nonneg_left henergy hcoef
  have hbracket :
      fullGap + (_root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1) * energy < 0 := by
    have hk : 0 < 1 - lambda := sub_pos.mpr hlambda1
    have hpoly : 0 < (1 - lambda) + (1 - lambda) ^ 2 / 2 := by
      positivity
    have htarget :
        -(3 / 2 : ℝ) * gap +
            (_root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1) * (lambda * gap) =
          -((1 - lambda) + (1 - lambda) ^ 2 / 2) * gap := by
      unfold _root_.GD.N0232.N0720.N1465.d015694
      ring
    have hle :
        fullGap + (_root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1) * energy ≤
          -(3 / 2 : ℝ) * gap +
            (_root_.GD.N0232.N0720.N1465.d015694 lambda + 5 / 4 - 1) * (lambda * gap) :=
      add_le_add hfull hterm
    rw [htarget] at hle
    have hneg :
        -((1 - lambda) + (1 - lambda) ^ 2 / 2) * gap < 0 := by
      rw [neg_mul]
      exact neg_lt_zero.mpr (mul_pos hpoly hgap)
    exact hle.trans_lt hneg
  exact mul_neg_of_pos_of_neg hba hbracket



theorem d015697
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (henergy : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) ≤
        lambda * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (_root_.GD.N0232.N0720.N1465.d015694 lambda))
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4)) := by
  intro theta
  let P := _root_.GD.N0232.N0720.N1080.d014171 m n theta
  let base : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - theta.location
  let correction := _root_.GD.N0232.N0720.N1082.d015379 m n hm hn U
  have hbase : MemLp base 2 P := by
    simpa [P, base] using _root_.GD.N0232.N0720.N1080.d014177 m n hm hn theta
  have hcorrection : MemLp correction 2 P := by
    simpa [P, correction] using
      _root_.GD.N0232.N0720.N1082.d015385 m n hm hn theta U
  have hquadratic := _root_.GD.N0232.N0720.N1082.d015377
    P base correction hbase hcorrection (5 / 4) (_root_.GD.N0232.N0720.N1465.d015694 lambda)
  have herror (c : ℝ) :
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U c omega -
          theta.location) =
        fun omega ↦ base omega + c * correction omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1082.d015381]
    dsimp only [base, correction]
    ring
  have hfull :
      _root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
          _root_.GD.N0141.d006684 P base ≤
        -(3 / 2 : ℝ) *
          _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    have hfun : (fun omega ↦ base omega + correction omega) =
        (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega -
          theta.location) := by
      rw [herror 1]
      funext omega
      ring
    rw [hfun]
    simpa [P, base, _root_.GD.N0232.N0720.N1080.d014171] using
      _root_.GD.N0232.N0720.N1085.d015413
        m n hm hn U theta.location theta.scale₁ theta.scale₂
          theta.scale₁_pos theta.scale₂_pos
  have hnegative := _root_.GD.N0232.N0720.N1465.d015696
    hfull (henergy theta)
    (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U theta.scale₁_pos theta.scale₂_pos)
    hlambda0 hlambda1
  have hstrict :
      _root_.GD.N0141.d006684 P
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U
            (_root_.GD.N0232.N0720.N1465.d015694 lambda) omega - theta.location) <
        _root_.GD.N0141.d006684 P
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U
            (5 / 4) omega - theta.location) := by
    rw [herror (_root_.GD.N0232.N0720.N1465.d015694 lambda), herror (5 / 4)]
    apply sub_neg.mp
    rw [hquadratic]
    simpa [P, correction] using hnegative
  have hupperPos :
      0 < _root_.GD.N0141.d006684 P
        (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U
          (5 / 4) omega - theta.location) :=
    lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1082.d015389, _root_.GD.N0232.N0720.N1082.d015389]
  exact (ENNReal.ofReal_lt_ofReal_iff hupperPos).2 hstrict










theorem d015698
    {a b fullGap energy gap lambda : ℝ}
    (hfull : fullGap ≤ -(3 / 2 : ℝ) * gap)
    (henergy : energy ≤ lambda * gap)
    (hgap : 0 < gap)
    (hcoef : 0 ≤ a + b - 1)
    (hstep : a < b)
    (hthreshold : lambda * (a + b - 1) < 3 / 2) :
    (b - a) * (fullGap + (b + a - 1) * energy) < 0 := by
  have hterm :
      (b + a - 1) * energy ≤ (b + a - 1) * (lambda * gap) := by
    apply mul_le_mul_of_nonneg_left henergy
    linarith
  have hle :
      fullGap + (b + a - 1) * energy ≤
        -(3 / 2 : ℝ) * gap + (b + a - 1) * (lambda * gap) :=
    add_le_add hfull hterm
  have htarget :
      -(3 / 2 : ℝ) * gap + (b + a - 1) * (lambda * gap) =
        (lambda * (a + b - 1) - 3 / 2) * gap := by
    ring
  rw [htarget] at hle
  have hright : (lambda * (a + b - 1) - 3 / 2) * gap < 0 := by
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hthreshold) hgap
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hstep) (hle.trans_lt hright)




theorem d015699
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {lambda a b : ℝ}
    (hcoef : 0 ≤ a + b - 1)
    (hstep : a < b)
    (hthreshold : lambda * (a + b - 1) < 3 / 2)
    (henergy : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) ≤
        lambda * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U b)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) := by
  intro theta
  let P := _root_.GD.N0232.N0720.N1080.d014171 m n theta
  let base : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - theta.location
  let correction := _root_.GD.N0232.N0720.N1082.d015379 m n hm hn U
  have hbase : MemLp base 2 P := by
    simpa [P, base] using _root_.GD.N0232.N0720.N1080.d014177 m n hm hn theta
  have hcorrection : MemLp correction 2 P := by
    simpa [P, correction] using
      _root_.GD.N0232.N0720.N1082.d015385 m n hm hn theta U
  have hquadratic := _root_.GD.N0232.N0720.N1082.d015377
    P base correction hbase hcorrection a b
  have herror (c : ℝ) :
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U c omega -
          theta.location) =
        fun omega ↦ base omega + c * correction omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1082.d015381]
    dsimp only [base, correction]
    ring
  have hfull :
      _root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
          _root_.GD.N0141.d006684 P base ≤
        -(3 / 2 : ℝ) *
          _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    have hfun : (fun omega ↦ base omega + correction omega) =
        (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega -
          theta.location) := by
      rw [herror 1]
      funext omega
      ring
    rw [hfun]
    simpa [P, base, _root_.GD.N0232.N0720.N1080.d014171] using
      _root_.GD.N0232.N0720.N1085.d015413
        m n hm hn U theta.location theta.scale₁ theta.scale₂
          theta.scale₁_pos theta.scale₂_pos
  have hnegative := _root_.GD.N0232.N0720.N1465.d015698
    hfull (henergy theta)
    (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U theta.scale₁_pos theta.scale₂_pos)
    hcoef hstep hthreshold
  have hstrict :
      _root_.GD.N0141.d006684 P
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U b omega -
            theta.location) <
        _root_.GD.N0141.d006684 P
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega -
            theta.location) := by
    rw [herror b, herror a]
    apply sub_neg.mp
    rw [hquadratic]
    simpa [P, correction, add_comm] using hnegative
  have hupperPos :
      0 < _root_.GD.N0141.d006684 P
        (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega -
          theta.location) :=
    lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1082.d015389, _root_.GD.N0232.N0720.N1082.d015389]
  exact (ENNReal.ofReal_lt_ofReal_iff hupperPos).2 hstrict





def d015700 (lambda : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1465.d015694 lambda + (1 - lambda) / 4



def d015701 (lambda : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1465.d015694 lambda + (1 - lambda) / 2

theorem d015702
    {lambda : ℝ} (hlambda : lambda < 1) :
    _root_.GD.N0232.N0720.N1465.d015694 lambda < _root_.GD.N0232.N0720.N1465.d015700 lambda := by
  unfold _root_.GD.N0232.N0720.N1465.d015700
  linarith

theorem d015703
    {lambda : ℝ} (hlambda : lambda < 1) :
    _root_.GD.N0232.N0720.N1465.d015700 lambda < _root_.GD.N0232.N0720.N1465.d015701 lambda := by
  unfold _root_.GD.N0232.N0720.N1465.d015700 _root_.GD.N0232.N0720.N1465.d015701
  linarith

theorem d015704
    {lambda : ℝ} (hlambda : lambda < 1) :
    0 ≤ _root_.GD.N0232.N0720.N1465.d015694 lambda + _root_.GD.N0232.N0720.N1465.d015700 lambda - 1 := by
  simp only [_root_.GD.N0232.N0720.N1465.d015700, _root_.GD.N0232.N0720.N1465.d015694]
  linarith

theorem d015705
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1) :
    lambda *
        (_root_.GD.N0232.N0720.N1465.d015694 lambda + _root_.GD.N0232.N0720.N1465.d015700 lambda - 1) <
      3 / 2 := by
  have hprod : 0 < (1 - lambda) * (6 - 5 * lambda) := by
    exact mul_pos (sub_pos.mpr hlambda1) (by linarith)
  simp only [_root_.GD.N0232.N0720.N1465.d015700, _root_.GD.N0232.N0720.N1465.d015694]
  nlinarith

theorem d015706
    {lambda : ℝ} (hlambda : lambda < 1) :
    0 ≤ _root_.GD.N0232.N0720.N1465.d015694 lambda + _root_.GD.N0232.N0720.N1465.d015701 lambda - 1 := by
  simp only [_root_.GD.N0232.N0720.N1465.d015701, _root_.GD.N0232.N0720.N1465.d015694]
  linarith

theorem d015707
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1) :
    lambda * (_root_.GD.N0232.N0720.N1465.d015694 lambda + _root_.GD.N0232.N0720.N1465.d015701 lambda - 1) <
      3 / 2 := by
  have hsquare : 0 < (1 - lambda) ^ 2 := sq_pos_of_pos (sub_pos.mpr hlambda1)
  simp only [_root_.GD.N0232.N0720.N1465.d015701, _root_.GD.N0232.N0720.N1465.d015694]
  nlinarith



theorem d015708
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (henergy : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) ≤
        lambda * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (_root_.GD.N0232.N0720.N1465.d015700 lambda))
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (_root_.GD.N0232.N0720.N1465.d015694 lambda)) := by
  exact _root_.GD.N0232.N0720.N1465.d015699 m n hm hn U
    (_root_.GD.N0232.N0720.N1465.d015704 hlambda1)
    (_root_.GD.N0232.N0720.N1465.d015702 hlambda1)
    (_root_.GD.N0232.N0720.N1465.d015705 hlambda0 hlambda1) henergy



theorem d015709
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (henergy : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) ≤
        lambda * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (_root_.GD.N0232.N0720.N1465.d015701 lambda))
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (_root_.GD.N0232.N0720.N1465.d015694 lambda)) := by
  exact _root_.GD.N0232.N0720.N1465.d015699 m n hm hn U
    (_root_.GD.N0232.N0720.N1465.d015706 hlambda1)
    (by
      unfold _root_.GD.N0232.N0720.N1465.d015701
      linarith)
    (_root_.GD.N0232.N0720.N1465.d015707 hlambda0 hlambda1) henergy

end

end GD.N0232.N0720.N1465

#print axioms _root_.GD.N0232.N0720.N1465.d015697
#print axioms _root_.GD.N0232.N0720.N1465.d015699
#print axioms _root_.GD.N0232.N0720.N1465.d015708
#print axioms _root_.GD.N0232.N0720.N1465.d015709
