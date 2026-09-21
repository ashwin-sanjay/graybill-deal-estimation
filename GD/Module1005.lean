import GD.Module1004
import GD.Module0227
































open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1171

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1170
open _root_.GD.N0232.N0720.N1174
open _root_.GD.N0233.N0728
open _root_.GD.N0230.N0589




def d015982
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015945 rho weight x ^ 2 /
    _root_.GD.N0232.N0720.N1173.d015940 rho weight x




def d015983
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1171.d015982 rho weight x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2


theorem d015984
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) (c : ℝ)
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1173.d015940 rho (c • weight) x =
      c * _root_.GD.N0232.N0720.N1173.d015940 rho weight x := by
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088 _root_.GD.N0232.N0720.N1173.d015939
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with theta
  ring


theorem d015985
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) (c : ℝ)
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1173.d015945 rho (c • weight) x =
      c * _root_.GD.N0232.N0720.N1173.d015945 rho weight x := by
  unfold _root_.GD.N0232.N0720.N1173.d015945 _root_.GD.N0232.N0720.N1173.d015939
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with theta
  ring



theorem d015986
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) {c : ℝ} (hc : 0 < c)
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1171.d015982 rho (c • weight) x =
      c * _root_.GD.N0232.N0720.N1171.d015982 rho weight x := by
  unfold _root_.GD.N0232.N0720.N1171.d015982
  rw [_root_.GD.N0232.N0720.N1171.d015985, _root_.GD.N0232.N0720.N1171.d015984]
  field_simp [ne_of_gt hc]



theorem d015987
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) {c : ℝ} (hc : 0 < c)
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) :
    _root_.GD.N0232.N0720.N1171.d015983 rho (c • weight) =
      c * _root_.GD.N0232.N0720.N1171.d015983 rho weight := by
  unfold _root_.GD.N0232.N0720.N1171.d015983
  have hpoint :
      _root_.GD.N0232.N0720.N1171.d015982 rho (c • weight) =
        fun x ↦ c * _root_.GD.N0232.N0720.N1171.d015982 rho weight x := by
    funext x
    exact _root_.GD.N0232.N0720.N1171.d015986 rho hc weight x
  rw [hpoint, integral_const_mul]






theorem d015988
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hfullJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 (_root_.GD.N0232.N0720.N1173.d015944 rho)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 rho weight)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          (_root_.GD.N0232.N0720.N1173.d015944 rho) (_root_.GD.N0232.N0720.N1173.d015943 rho weight))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho weight x ≠ 0) :
    _root_.GD.N0232.N0720.N1171.d015983 rho weight =
      _root_.GD.N0232.N0720.N1173.d015956 rho weight := by
  exact (_root_.GD.N0232.N0720.N1173.d015957
    rho weight hfullJoint hcutJoint htax hmoments).symm








theorem d015989
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hfullJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015944 rho)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 rho (fun theta ↦ h theta ^ 2))).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 rho)
          (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2))
          (_root_.GD.N0232.N0720.N1173.d015944 rho)
          (_root_.GD.N0232.N0720.N1173.d015943 rho (fun theta ↦ h theta ^ 2)))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta *
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 *
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x ≠ 0)
    (hfullMoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1173.d015938 theta)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0)
    (hpair : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun z ↦
            _root_.GD.N0232.N0720.N1174.d015960 rho x z *
              _root_.GD.N0232.N0720.N1174.d015961 (fun theta ↦ h theta ^ 2) z)
          ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) ∧
      Integrable
          (fun z ↦
            _root_.GD.N0232.N0720.N1174.d015960 rho x z *
              _root_.GD.N0232.N0720.N1174.d015961 (fun theta ↦ h theta ^ 2) z ^ 2)
          ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hdeficitIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1174.d015964 rho (fun theta ↦ h theta ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hdirichletIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1174.d015965 rho (fun theta ↦ h theta ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    _root_.GD.N0232.N0720.N1171.d015983 rho (fun theta ↦ h theta ^ 2) ≤
      _root_.GD.N0232.N0720.N1174.d015966 rho (fun theta ↦ h theta ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1171.d015988
    rho (fun theta ↦ h theta ^ 2)
      hfullJoint hcutJoint htax hmoments]
  exact _root_.GD.N0232.N0720.N1174.d015972
    rho h hfullJoint hcutJoint htax hmoments hfullMoments hpair
      hdeficitIntegrable hdirichletIntegrable








theorem d015990
    {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (A : (_root_.GD.N0232.N0720.N1173.d015933 → ℝ) →ₗ[ℝ] Y)
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hone : ‖A weight‖ ^ 2 =
      _root_.GD.N0232.N0720.N1171.d015982 rho weight x)
    (htwo : ‖A ((2 : ℝ) • weight)‖ ^ 2 =
      _root_.GD.N0232.N0720.N1171.d015982 rho ((2 : ℝ) • weight) x) :
    _root_.GD.N0232.N0720.N1171.d015982 rho weight x = 0 := by
  have hlinear : A ((2 : ℝ) • weight) = (2 : ℝ) • A weight :=
    A.map_smul_of_tower (2 : ℝ) weight
  have hleft : ‖A ((2 : ℝ) • weight)‖ ^ 2 =
      4 * ‖A weight‖ ^ 2 := by
    rw [hlinear, norm_smul]
    norm_num
    ring
  have hright :
      _root_.GD.N0232.N0720.N1171.d015982 rho ((2 : ℝ) • weight) x =
        2 * _root_.GD.N0232.N0720.N1171.d015982 rho weight x :=
    _root_.GD.N0232.N0720.N1171.d015986 rho (by norm_num) weight x
  rw [hleft, hone, hright] at htwo
  linarith




theorem d015991
    {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (A : (_root_.GD.N0232.N0720.N1173.d015933 → ℝ) →ₗ[ℝ] Y)
    (hrep : ∀ weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ,
      ‖A weight‖ ^ 2 = _root_.GD.N0232.N0720.N1171.d015983 rho weight)
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) :
    _root_.GD.N0232.N0720.N1171.d015983 rho weight = 0 := by
  have hlinear : A ((2 : ℝ) • weight) = (2 : ℝ) • A weight :=
    A.map_smul_of_tower (2 : ℝ) weight
  have hleft : ‖A ((2 : ℝ) • weight)‖ ^ 2 =
      4 * ‖A weight‖ ^ 2 := by
    rw [hlinear, norm_smul]
    norm_num
    ring
  have hright :
      _root_.GD.N0232.N0720.N1171.d015983 rho ((2 : ℝ) • weight) =
        2 * _root_.GD.N0232.N0720.N1171.d015983 rho weight :=
    _root_.GD.N0232.N0720.N1171.d015987
      rho (by norm_num) weight
  have htwo := hrep ((2 : ℝ) • weight)
  rw [hleft, hrep weight, hright] at htwo
  linarith




def d015992
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1171.d015982 rho (fun theta ↦ h theta ^ 2) x




theorem d015993
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) (c : ℝ)
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1171.d015992 rho (c • h) x =
      c ^ 2 * _root_.GD.N0232.N0720.N1171.d015992 rho h x := by
  have hweights :
      (fun theta ↦ (c • h) theta ^ 2) =
        (c ^ 2) • (fun theta ↦ h theta ^ 2) := by
    funext theta
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  by_cases hc : c = 0
  · subst c
    unfold _root_.GD.N0232.N0720.N1171.d015992 _root_.GD.N0232.N0720.N1171.d015982
    rw [hweights, _root_.GD.N0232.N0720.N1171.d015985, _root_.GD.N0232.N0720.N1171.d015984]
    simp
  · have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    unfold _root_.GD.N0232.N0720.N1171.d015992
    rw [hweights,
      _root_.GD.N0232.N0720.N1171.d015986 rho hc2]



section FixedProfile

variable
    {H Y : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]





def d015994
    (current : H →ₗ[ℝ] Y)
    (hcontractive : ∀ u, ‖current u‖ ≤ ‖u‖) : H →L[ℝ] Y :=
  LinearMap.mkContinuous current 1 (by simpa using hcontractive)

@[simp]
theorem d015995
    (current : H →ₗ[ℝ] Y)
    (hcontractive : ∀ u, ‖current u‖ ≤ ‖u‖) (u : H) :
    _root_.GD.N0232.N0720.N1171.d015994 current hcontractive u = current u :=
  rfl

theorem d015996
    (current : H →ₗ[ℝ] Y)
    (hcontractive : ∀ u, ‖current u‖ ≤ ‖u‖) :
    ‖_root_.GD.N0232.N0720.N1171.d015994 current hcontractive‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun u ↦ by
    simpa using hcontractive u



theorem d015997
    (current : H →ₗ[ℝ] Y)
    (hcontractive : ∀ u, ‖current u‖ ≤ ‖u‖)
    (y : _root_.GD.N0233.N0728.d003239 (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive))
    {u : H}
    (hu : _root_.GD.N0232.N0720.N1171.d015994 current hcontractive u = y.1) :
    ‖u‖ ^ 2 =
      _root_.GD.N0233.N0728.d003247 (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive) y +
        ‖_root_.GD.N0233.N0728.d003226 (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive) u‖ ^ 2 :=
  _root_.GD.N0233.N0728.d003249
    (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive) y hu




theorem d015998
    (current : H →ₗ[ℝ] Y)
    (hcontractive : ∀ u, ‖current u‖ ≤ ‖u‖)
    (y : _root_.GD.N0233.N0728.d003239 (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive))
    {u : H}
    (hu : _root_.GD.N0232.N0720.N1171.d015994 current hcontractive u = y.1)
    (horthogonal : u ∈
      (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive).ker.orthogonal) :
    u = _root_.GD.N0233.N0728.d003242
      (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive) y :=
  _root_.GD.N0233.N0728.d003245
    (_root_.GD.N0232.N0720.N1171.d015994 current hcontractive) y hu horthogonal

end FixedProfile

end

end N1171
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1171.d015986
#print axioms _root_.GD.N0232.N0720.N1171.d015989
#print axioms _root_.GD.N0232.N0720.N1171.d015990
#print axioms _root_.GD.N0232.N0720.N1171.d015991
#print axioms _root_.GD.N0232.N0720.N1171.d015993
#print axioms _root_.GD.N0232.N0720.N1171.d015997
