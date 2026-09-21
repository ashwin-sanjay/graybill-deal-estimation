import Mathlib














namespace GD
namespace N0232
namespace N0720
namespace N1060

noncomputable section



def d001880 (s m u : ℝ) : ℝ :=
  m * (s - u) ^ 2



def d001881 (m u l mu t : ℝ) : ℝ :=
  (m * u + t * l * mu) / (m + t * l)


def d001882 (s m u l mu t : ℝ) : ℝ :=
  (s * (m + t * l) - (m * u + t * l * mu)) ^ 2 /
    (m + t * l)



def d001883 (s u l mu : ℝ) : ℝ :=
  l * ((s - mu) ^ 2 - (u - mu) ^ 2)


def d001884 (m u l mu : ℝ) : ℝ :=
  l ^ 2 * (u - mu) ^ 2 / m



theorem d001885
    (s m u l mu t : ℝ) (hdenom : m + t * l ≠ 0) :
    _root_.GD.N0232.N0720.N1060.d001882 s m u l mu t =
      _root_.GD.N0232.N0720.N1060.d001880 s m u + t * _root_.GD.N0232.N0720.N1060.d001883 s u l mu +
        t ^ 2 * l ^ 2 * (u - mu) ^ 2 / (m + t * l) := by
  unfold _root_.GD.N0232.N0720.N1060.d001882 _root_.GD.N0232.N0720.N1060.d001880 _root_.GD.N0232.N0720.N1060.d001883
  field_simp
  ring



theorem d001886
    (s m u l mu t : ℝ) (ht : t ≠ 0) (hdenom : m + t * l ≠ 0) :
    (_root_.GD.N0232.N0720.N1060.d001882 s m u l mu t -
        _root_.GD.N0232.N0720.N1060.d001880 s m u) / t =
      _root_.GD.N0232.N0720.N1060.d001883 s u l mu +
        t * l ^ 2 * (u - mu) ^ 2 / (m + t * l) := by
  rw [_root_.GD.N0232.N0720.N1060.d001885 s m u l mu t hdenom]
  field_simp
  ring


theorem d001887
    (m u l mu t : ℝ) (hm : 0 < m) (hl : 0 ≤ l) (ht : 0 ≤ t) :
    0 ≤ t ^ 2 * l ^ 2 * (u - mu) ^ 2 / (m + t * l) := by
  positivity



theorem d001888
    (m u l mu t : ℝ) (hm : 0 < m) (hl : 0 ≤ l) (ht : 0 ≤ t) :
    t ^ 2 * l ^ 2 * (u - mu) ^ 2 / (m + t * l) ≤
      t ^ 2 * _root_.GD.N0232.N0720.N1060.d001884 m u l mu := by
  unfold _root_.GD.N0232.N0720.N1060.d001884
  have hnum : 0 ≤ t ^ 2 * l ^ 2 * (u - mu) ^ 2 := by positivity
  have hdenom : 0 < m + t * l := by positivity
  have hle : m ≤ m + t * l := by
    nlinarith [mul_nonneg ht hl]
  have hmain := div_le_div_of_nonneg_left hnum hm hle
  calc
    (t ^ 2 * l ^ 2 * (u - mu) ^ 2) / (m + t * l) ≤
        (t ^ 2 * l ^ 2 * (u - mu) ^ 2) / m := hmain
    _ = t ^ 2 * (l ^ 2 * (u - mu) ^ 2 / m) := by ring


theorem d001889
    (s m u l mu t : ℝ) (hm : 0 < m) (hl : 0 ≤ l) (ht : 0 ≤ t) :
    _root_.GD.N0232.N0720.N1060.d001882 s m u l mu t ≤
      _root_.GD.N0232.N0720.N1060.d001880 s m u + t * _root_.GD.N0232.N0720.N1060.d001883 s u l mu +
        t ^ 2 * _root_.GD.N0232.N0720.N1060.d001884 m u l mu := by
  rw [_root_.GD.N0232.N0720.N1060.d001885 s m u l mu t (by positivity)]
  gcongr
  exact _root_.GD.N0232.N0720.N1060.d001888 m u l mu t hm hl ht



theorem d001890
    (s m u l mu : ℝ) (hm : 0 < m) (hl : 0 ≤ l)
    (hcurv : _root_.GD.N0232.N0720.N1060.d001884 m u l mu = 0) :
    0 ≤ _root_.GD.N0232.N0720.N1060.d001883 s u l mu := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hprod : l ^ 2 * (u - mu) ^ 2 = 0 := by
    unfold _root_.GD.N0232.N0720.N1060.d001884 at hcurv
    rcases div_eq_zero_iff.mp hcurv with hprod | hmzero
    · exact hprod
    · exact (hm0 hmzero).elim
  rcases mul_eq_zero.mp hprod with hlzero | huzero
  · have hl' : l = 0 := (sq_eq_zero_iff).mp hlzero
    simp [_root_.GD.N0232.N0720.N1060.d001883, hl']
  · have hu : u = mu := sub_eq_zero.mp ((sq_eq_zero_iff).mp huzero)
    subst u
    simp only [_root_.GD.N0232.N0720.N1060.d001883, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sub_zero]
    positivity



theorem d001891
    (s m u l mu : ℝ) (hm : 0 < m) (hl : 0 ≤ l)
    (hgrad : _root_.GD.N0232.N0720.N1060.d001883 s u l mu < 0) :
    0 < _root_.GD.N0232.N0720.N1060.d001884 m u l mu := by
  have hcurvNonneg : 0 ≤ _root_.GD.N0232.N0720.N1060.d001884 m u l mu := by
    unfold _root_.GD.N0232.N0720.N1060.d001884
    positivity
  exact lt_of_le_of_ne hcurvNonneg fun hzero ↦
    (not_le_of_gt hgrad)
      (_root_.GD.N0232.N0720.N1060.d001890
        s m u l mu hm hl hzero.symm)


def d001892
    (m u li lj mui muj : ℝ) : ℝ :=
  2 * (li * (u - mui)) * (lj * (u - muj)) / m

theorem d001893
    (m u li lj mui muj : ℝ) :
    _root_.GD.N0232.N0720.N1060.d001892 m u li lj mui muj =
      (2 / m) * (li * (u - mui)) * (lj * (u - muj)) := by
  unfold _root_.GD.N0232.N0720.N1060.d001892
  ring




theorem d001894
    (m z : ℝ) (hm : 0 < m) :
    0 ≤ (2 / m) * z ^ 2 := by
  positivity






theorem d001895
    (s u bound : ℝ) (hne : u ≠ s) :
    ∃ mu : ℝ, bound < (u - mu) ^ 2 - (s - mu) ^ 2 := by
  let d : ℝ := u - s
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  let mu : ℝ := (u + s) / 2 - (bound + 1) / (2 * d)
  refine ⟨mu, ?_⟩
  have hidentity : (u - mu) ^ 2 - (s - mu) ^ 2 = bound + 1 := by
    dsimp [mu, d]
    field_simp [hd]
    ring
  rw [hidentity]
  linarith



theorem d001896
    (s u : ℝ) (hne : u ≠ s) :
    ¬ ∃ muStar : ℝ, ∀ mu : ℝ,
      (u - mu) ^ 2 - (s - mu) ^ 2 ≤
        (u - muStar) ^ 2 - (s - muStar) ^ 2 := by
  rintro ⟨muStar, hmax⟩
  obtain ⟨mu, hmu⟩ := _root_.GD.N0232.N0720.N1060.d001895 s u
    ((u - muStar) ^ 2 - (s - muStar) ^ 2) hne
  exact (not_lt_of_ge (hmax mu)) hmu





theorem d001897
    (energy next violation curvature : ℝ)
    (hnext : 0 ≤ next) (hcurvature : 0 < curvature)
    (hdescent :
      next ≤ energy - violation ^ 2 / (4 * curvature)) :
    violation ^ 2 ≤ 4 * curvature * energy := by
  have hnonneg : 0 ≤ energy - violation ^ 2 / (4 * curvature) :=
    hnext.trans hdescent
  have hdenom : 0 < 4 * curvature := by positivity
  have hdiv : violation ^ 2 / (4 * curvature) ≤ energy := by linarith
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (div_le_iff₀ hdenom).mp hdiv



theorem d001898
    (energy next violation curvature : ℝ)
    (henergy : 0 < energy) (hnext : 0 ≤ next)
    (hcurvature : 0 < curvature)
    (hdescent :
      next ≤ energy - violation ^ 2 / (4 * curvature)) :
    violation ^ 2 / (curvature * energy) ≤ 4 := by
  have hdenom : 0 < curvature * energy := by positivity
  rw [div_le_iff₀ hdenom]
  nlinarith [_root_.GD.N0232.N0720.N1060.d001897
    energy next violation curvature hnext hcurvature hdescent]

end

end N1060
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1060.d001885
#print axioms _root_.GD.N0232.N0720.N1060.d001891
#print axioms _root_.GD.N0232.N0720.N1060.d001896
#print axioms _root_.GD.N0232.N0720.N1060.d001898
