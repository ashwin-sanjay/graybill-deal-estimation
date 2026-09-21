import GD.Module0990
import GD.Module0037












open MeasureTheory

namespace GD.N0232.N0720.N1083

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
open _root_.GD.N0230.N0672

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

noncomputable local instance d015710 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

noncomputable local instance d015711 : Nonempty _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨_root_.GD.N0232.N0720.N1080.d014169⟩

def d015712
    (_U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
    (fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - theta.location)

def d015713
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U)

def d015714
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
    (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega -
      theta.location)

def d015715
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U 1 theta -
    _root_.GD.N0232.N0720.N1083.d015712 m n hm hn U theta



def d015716
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  (_root_.GD.N0232.N0720.N1083.d015715 m n hm hn U theta -
    _root_.GD.N0232.N0720.N1083.d015713 m n hm hn U theta) / 2


def d015717
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  -_root_.GD.N0232.N0720.N1083.d015716 m n hm hn U theta /
    _root_.GD.N0232.N0720.N1083.d015713 m n hm hn U theta

def d015718
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1083.d015712 m n hm hn U theta -
    _root_.GD.N0232.N0720.N1083.d015716 m n hm hn U theta ^ 2 /
      _root_.GD.N0232.N0720.N1083.d015713 m n hm hn U theta




theorem d015719
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1083.d015713 m n hm hn U theta := by
  let P := _root_.GD.N0232.N0720.N1080.d014171 m n theta
  let base : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - theta.location
  let correction := _root_.GD.N0232.N0720.N1082.d015379 m n hm hn U
  have hbase : MemLp base 2 P := by
    simpa [P, base] using _root_.GD.N0232.N0720.N1080.d014177 m n hm hn theta
  have hcorrection : MemLp correction 2 P := by
    simpa [P, correction] using
      _root_.GD.N0232.N0720.N1082.d015385 m n hm hn theta U
  have hnonneg : 0 ≤ _root_.GD.N0141.d006684 P correction := by
    exact integral_nonneg fun _ ↦ sq_nonneg _
  apply lt_of_le_of_ne hnonneg
  intro hzeroRev
  have hzero : _root_.GD.N0141.d006684 P correction = 0 := hzeroRev.symm
  have hsqZero : (fun omega ↦ correction omega ^ 2) =ᵐ[P] 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (fun omega ↦ sq_nonneg (correction omega))
      hcorrection.integrable_sq).1
    simpa only [_root_.GD.N0141.d006684] using hzero
  have hcorrectionZero : correction =ᵐ[P] 0 := by
    filter_upwards [hsqZero] with omega homega
    have : correction omega ^ 2 = 0 := by simpa using homega
    exact sq_eq_zero_iff.mp this
  have hsumEq :
      _root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) =
        _root_.GD.N0141.d006684 P base := by
    unfold _root_.GD.N0141.d006684
    apply integral_congr_ae
    filter_upwards [hcorrectionZero] with omega homega
    simp only [Pi.zero_apply] at homega
    rw [homega]
    ring
  have herror :
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega -
          theta.location) =
        fun omega ↦ base omega + correction omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1082.d015381]
    dsimp only [base, correction]
    ring
  have hfull :
      _root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
          _root_.GD.N0141.d006684 P base ≤
        -(3 / 2 : ℝ) *
          _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    rw [← herror]
    simpa [P, base, _root_.GD.N0232.N0720.N1080.d014171] using
      _root_.GD.N0232.N0720.N1085.d015413
        m n hm hn U theta.location theta.scale₁ theta.scale₂
          theta.scale₁_pos theta.scale₂_pos
  rw [hsumEq, sub_self] at hfull
  have hgap :=
    _root_.GD.N0232.N0720.N1082.d015391 m n hm hn U theta.scale₁_pos theta.scale₂_pos
  nlinarith


theorem d015720
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U a theta =
      _root_.GD.N0232.N0720.N1083.d015712 m n hm hn U theta +
        2 * a * _root_.GD.N0232.N0720.N1083.d015716 m n hm hn U theta +
        a ^ 2 * _root_.GD.N0232.N0720.N1083.d015713 m n hm hn U theta := by
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
    P base correction hbase hcorrection 0 a
  have herror (c : ℝ) :
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U c omega -
          theta.location) =
        fun omega ↦ base omega + c * correction omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1082.d015381]
    dsimp only [base, correction]
    ring
  have hzero : (fun omega ↦ base omega + 0 * correction omega) = base := by
    funext omega
    ring
  rw [hzero] at hquadratic
  unfold _root_.GD.N0232.N0720.N1083.d015716 _root_.GD.N0232.N0720.N1083.d015715 _root_.GD.N0232.N0720.N1083.d015714
    _root_.GD.N0232.N0720.N1083.d015712 _root_.GD.N0232.N0720.N1083.d015713
  rw [herror a, herror 1]
  dsimp only [P, base, correction] at hquadratic ⊢
  simp only [one_mul, zero_mul, add_zero, sub_zero] at hquadratic ⊢
  nlinarith [hquadratic]


theorem d015721
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U a theta =
      _root_.GD.N0230.N0672.d000446
        (_root_.GD.N0232.N0720.N1083.d015718 m n hm hn U)
        (_root_.GD.N0232.N0720.N1083.d015713 m n hm hn U)
        (_root_.GD.N0232.N0720.N1083.d015717 m n hm hn U) a theta := by
  rw [_root_.GD.N0232.N0720.N1083.d015720]
  unfold _root_.GD.N0230.N0672.d000446 _root_.GD.N0232.N0720.N1083.d015718 _root_.GD.N0232.N0720.N1083.d015717
  exact _root_.GD.N0230.N0672.d000451
    (ne_of_gt (_root_.GD.N0232.N0720.N1083.d015719 m n hm hn U theta))


theorem d015722
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (5 / 4 : ℝ) ≤ _root_.GD.N0232.N0720.N1083.d015717 m n hm hn U theta := by
  let energy := _root_.GD.N0232.N0720.N1083.d015713 m n hm hn U theta
  let fullGap := _root_.GD.N0232.N0720.N1083.d015715 m n hm hn U theta
  have henergy : 0 < energy := by
    simpa only [energy] using _root_.GD.N0232.N0720.N1083.d015719 m n hm hn U theta
  have henergyGap : energy ≤
      _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    simpa only [energy, _root_.GD.N0232.N0720.N1083.d015713, _root_.GD.N0232.N0720.N1080.d014171] using
      _root_.GD.N0232.N0720.N1082.d015392
        m n hm hn U theta.location theta.scale₁ theta.scale₂
          theta.scale₁_pos theta.scale₂_pos
  have hfull : fullGap ≤
      -(3 / 2 : ℝ) *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    unfold fullGap _root_.GD.N0232.N0720.N1083.d015715 _root_.GD.N0232.N0720.N1083.d015714 _root_.GD.N0232.N0720.N1083.d015712
    simpa [_root_.GD.N0232.N0720.N1080.d014171] using
      _root_.GD.N0232.N0720.N1085.d015413
        m n hm hn U theta.location theta.scale₁ theta.scale₂
          theta.scale₁_pos theta.scale₂_pos
  have hfullEnergy : fullGap ≤ -(3 / 2 : ℝ) * energy := by
    nlinarith
  have hvertexMul :
      _root_.GD.N0232.N0720.N1083.d015717 m n hm hn U theta * energy =
        (energy - fullGap) / 2 := by
    change (-((fullGap - energy) / 2) / energy) * energy =
      (energy - fullGap) / 2
    field_simp [ne_of_gt henergy]
    <;> ring
  nlinarith [hvertexMul]


def d015723
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) : ℝ :=
  _root_.GD.N0230.N0672.d000445 (_root_.GD.N0232.N0720.N1083.d015717 m n hm hn U)

theorem d015724
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    BddBelow (Set.range (_root_.GD.N0232.N0720.N1083.d015717 m n hm hn U)) := by
  refine ⟨5 / 4, ?_⟩
  rintro _ ⟨theta, rfl⟩
  exact _root_.GD.N0232.N0720.N1083.d015722 m n hm hn U theta

theorem d015725
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    (5 / 4 : ℝ) ≤ _root_.GD.N0232.N0720.N1083.d015723 m n hm hn U := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨theta, rfl⟩
  exact _root_.GD.N0232.N0720.N1083.d015722 m n hm hn U theta

theorem d015726
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    0 < _root_.GD.N0232.N0720.N1083.d015723 m n hm hn U := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5 / 4)
    (_root_.GD.N0232.N0720.N1083.d015725 m n hm hn U)



theorem d015727
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {a : ℝ} (ha : a < _root_.GD.N0232.N0720.N1083.d015723 m n hm hn U) :
    ∀ theta,
      _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U
          (_root_.GD.N0232.N0720.N1083.d015723 m n hm hn U) theta <
        _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U a theta := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1083.d015721,
    _root_.GD.N0232.N0720.N1083.d015721]
  exact _root_.GD.N0230.N0672.d000448
    (_root_.GD.N0232.N0720.N1083.d015718 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015713 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015717 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015719 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015724 m n hm hn U) ha theta



theorem d015728
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {b : ℝ} (hb : _root_.GD.N0232.N0720.N1083.d015723 m n hm hn U < b) :
    ∃ theta,
      _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U
          (_root_.GD.N0232.N0720.N1083.d015723 m n hm hn U) theta <
        _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U b theta := by
  obtain ⟨theta, htheta⟩ := _root_.GD.N0230.N0672.d000449
    (_root_.GD.N0232.N0720.N1083.d015718 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015713 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015717 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015719 m n hm hn U)
    (_root_.GD.N0232.N0720.N1083.d015724 m n hm hn U) hb
  refine ⟨theta, ?_⟩
  simpa only [_root_.GD.N0232.N0720.N1083.d015723,
    _root_.GD.N0232.N0720.N1083.d015721] using htheta



theorem d015729
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {a : ℝ} (ha : a < _root_.GD.N0232.N0720.N1083.d015723 m n hm hn U) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U
        (_root_.GD.N0232.N0720.N1083.d015723 m n hm hn U))
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) := by
  intro theta
  have hstrict := _root_.GD.N0232.N0720.N1083.d015727
    m n hm hn U ha theta
  have hupperPos : 0 < _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U a theta :=
    lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1082.d015389, _root_.GD.N0232.N0720.N1082.d015389]
  exact (ENNReal.ofReal_lt_ofReal_iff hupperPos).2 hstrict



theorem d015730
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U
        (_root_.GD.N0232.N0720.N1083.d015723 m n hm hn U))
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  simpa only [_root_.GD.N0232.N0720.N1082.d015388 m n hm hn U] using
    (_root_.GD.N0232.N0720.N1083.d015729
      m n hm hn U (_root_.GD.N0232.N0720.N1083.d015726 m n hm hn U))



theorem d015731
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {b : ℝ} (hb : _root_.GD.N0232.N0720.N1083.d015723 m n hm hn U < b) :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U b)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U
        (_root_.GD.N0232.N0720.N1083.d015723 m n hm hn U)) := by
  obtain ⟨theta, hstrict⟩ :=
    _root_.GD.N0232.N0720.N1083.d015728
      m n hm hn U hb
  intro hweak
  have hlowerNonneg :
      0 ≤ _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U
        (_root_.GD.N0232.N0720.N1083.d015723 m n hm hn U) theta :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hupperPos : 0 < _root_.GD.N0232.N0720.N1083.d015714 m n hm hn U b theta :=
    hlowerNonneg.trans_lt hstrict
  have hofReal :
      ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1083.d015714 m n hm hn U
            (_root_.GD.N0232.N0720.N1083.d015723 m n hm hn U) theta) <
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1083.d015714 m n hm hn U b theta) :=
    (ENNReal.ofReal_lt_ofReal_iff hupperPos).2 hstrict
  have hweakTheta := hweak theta
  rw [_root_.GD.N0232.N0720.N1082.d015389, _root_.GD.N0232.N0720.N1082.d015389] at hweakTheta
  exact (not_le_of_gt hofReal) hweakTheta

end

end GD.N0232.N0720.N1083

#print axioms _root_.GD.N0232.N0720.N1083.d015719
#print axioms _root_.GD.N0232.N0720.N1083.d015721
#print axioms _root_.GD.N0232.N0720.N1083.d015729
#print axioms _root_.GD.N0232.N0720.N1083.d015730
#print axioms _root_.GD.N0232.N0720.N1083.d015731
