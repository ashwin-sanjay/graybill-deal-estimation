import GD.Module0727
import GD.Module0059




























open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0815

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616



def d010924 {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : ℝ :=
  1 / theta.scale i ^ 2

theorem d010925
    {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0815.d010924 theta i := by
  unfold _root_.GD.N0232.N0719.N0815.d010924
  exact one_div_pos.mpr (sq_pos_of_pos (theta.scale_pos i))


def d010926 {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  ∑ i, _root_.GD.N0232.N0719.N0815.d010924 theta i

theorem d010927
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0815.d010926 theta := by
  let i : Fin k := ⟨0, hk⟩
  unfold _root_.GD.N0232.N0719.N0815.d010926
  exact Finset.sum_pos' (fun j _ ↦ (_root_.GD.N0232.N0719.N0815.d010925 theta j).le)
    ⟨i, Finset.mem_univ i, _root_.GD.N0232.N0719.N0815.d010925 theta i⟩




def d010928
    {k : ℕ} (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  (∑ i ∈ activeᶜ, _root_.GD.N0232.N0719.N0815.d010924 theta i) /
    _root_.GD.N0232.N0719.N0815.d010926 theta

theorem d010929
    {k : ℕ}
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0815.d010924 (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) i =
      (1 / dilation ^ 2) * _root_.GD.N0232.N0719.N0815.d010924 theta i := by
  unfold _root_.GD.N0232.N0719.N0815.d010924
  simp only [_root_.GD.N0232.N0719.N0845.d010883, mul_pow]
  field_simp [hdilation.ne', (theta.scale_pos i).ne']

theorem d010930
    {k : ℕ}
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010926 (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      (1 / dilation ^ 2) * _root_.GD.N0232.N0719.N0815.d010926 theta := by
  unfold _root_.GD.N0232.N0719.N0815.d010926
  simp_rw [_root_.GD.N0232.N0719.N0815.d010929 shift dilation hdilation theta]
  exact (Finset.mul_sum _ _ _).symm



theorem d010931
    {k : ℕ} (hk : 0 < k) (active : Finset (Fin k))
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 active
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      _root_.GD.N0232.N0719.N0815.d010928 active theta := by
  unfold _root_.GD.N0232.N0719.N0815.d010928
  rw [_root_.GD.N0232.N0719.N0815.d010930]
  simp_rw [_root_.GD.N0232.N0719.N0815.d010929 shift dilation hdilation theta]
  rw [← Finset.mul_sum]
  field_simp [hdilation.ne', (_root_.GD.N0232.N0719.N0815.d010927 hk theta).ne']


theorem d010932
    {k : ℕ} (hk : 0 < k) (active : Finset (Fin k))
    (epsilon shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 active
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) ≤ epsilon ↔
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon := by
  rw [_root_.GD.N0232.N0719.N0815.d010931 hk active shift dilation hdilation theta]


def d010933
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ENNReal :=
  _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d /
    _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta


theorem d010934
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) =
      _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes theta d := by
  unfold _root_.GD.N0232.N0719.N0815.d010933
  rw [_root_.GD.N0232.N0719.N0842.d010920
    k sizes shift dilation hdilation theta d hd]
  rw [_root_.GD.N0232.N0719.N0845.d010903
    k sizes hk hsizes shift dilation hdilation theta]
  exact ENNReal.mul_div_mul_left _ _
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hdilation)).ne'
    (ENNReal.ofReal_ne_top)



def d010935
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
  (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ENNReal :=
  ⨆ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
    _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes theta.1 d


theorem d010936
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {e d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ}
    (hed : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) :
    _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active epsilon e ≤
      _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active epsilon d := by
  unfold _root_.GD.N0232.N0719.N0815.d010935
  apply iSup_mono
  intro theta
  exact ENNReal.div_le_div_right (hed theta.1)
    (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta.1)



theorem d010937
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active epsilon
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) =
      _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active epsilon d := by
  apply le_antisymm
  · unfold _root_.GD.N0232.N0719.N0815.d010935
    apply iSup_le
    intro eta
    let theta : _root_.GD.N0232.N0719.N0859.d010809 k :=
      _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
        (inv_pos.mpr hdilation) eta.1
    have heta : _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta = eta.1 :=
      _root_.GD.N0232.N0719.N0842.d010919 shift dilation hdilation eta.1
    have hthetaCollar : _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon := by
      rw [← _root_.GD.N0232.N0719.N0815.d010931 (by omega : 0 < k) active
        shift dilation hdilation theta, heta]
      exact eta.2
    calc
      _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes eta.1
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) =
          _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes
            (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta)
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) := by rw [heta]
      _ = _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes theta d :=
        _root_.GD.N0232.N0719.N0815.d010934
          k sizes hk hsizes shift dilation hdilation theta d hd
      _ ≤ ⨆ z : {z : _root_.GD.N0232.N0719.N0859.d010809 k //
            _root_.GD.N0232.N0719.N0815.d010928 active z ≤ epsilon},
          _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes z.1 d :=
        le_iSup (fun z : {z : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active z ≤ epsilon} ↦
            _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes z.1 d)
          ⟨theta, hthetaCollar⟩
  · unfold _root_.GD.N0232.N0719.N0815.d010935
    apply iSup_le
    intro theta
    let eta : _root_.GD.N0232.N0719.N0859.d010809 k :=
      _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta.1
    have hetaCollar : _root_.GD.N0232.N0719.N0815.d010928 active eta ≤ epsilon := by
      rw [_root_.GD.N0232.N0719.N0815.d010931 (by omega : 0 < k) active
        shift dilation hdilation theta.1]
      exact theta.2
    calc
      _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes theta.1 d =
          _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes eta
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) := by
        symm
        exact _root_.GD.N0232.N0719.N0815.d010934
          k sizes hk hsizes shift dilation hdilation theta.1 d hd
      _ ≤ ⨆ z : {z : _root_.GD.N0232.N0719.N0859.d010809 k //
            _root_.GD.N0232.N0719.N0815.d010928 active z ≤ epsilon},
          _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes z.1
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) :=
        le_iSup (fun z : {z : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active z ≤ epsilon} ↦
            _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes z.1
              (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d))
          ⟨eta, hetaCollar⟩


def d010938 (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

theorem d010939 (n : ℕ) : 0 ≤ _root_.GD.N0232.N0719.N0815.d010938 n := by
  exact (one_div_pos.mpr (by positivity : 0 < (n + 1 : ℝ))).le


def d010940
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ENNReal :=
  ⨅ n : ℕ,
    _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active (_root_.GD.N0232.N0719.N0815.d010938 n) d


def d010941
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ENNReal :=
  ⨆ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
    _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes theta d

@[simp] theorem d010942
    {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 (Finset.univ : Finset (Fin k)) theta = 0 := by
  simp [_root_.GD.N0232.N0719.N0815.d010928]



theorem d010943
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes Finset.univ epsilon d =
      _root_.GD.N0232.N0719.N0815.d010941 k sizes hk hsizes d := by
  apply le_antisymm
  · unfold _root_.GD.N0232.N0719.N0815.d010935 _root_.GD.N0232.N0719.N0815.d010941
    apply iSup_le
    intro theta
    exact le_iSup
      (fun eta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
        _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes eta d) theta.1
  · unfold _root_.GD.N0232.N0719.N0815.d010935 _root_.GD.N0232.N0719.N0815.d010941
    apply iSup_le
    intro theta
    exact le_iSup
      (fun eta : {eta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 (Finset.univ : Finset (Fin k)) eta ≤ epsilon} ↦
        _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes eta.1 d)
      ⟨theta, by simpa using hepsilon⟩



theorem d010944
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes Finset.univ d =
      _root_.GD.N0232.N0719.N0815.d010941 k sizes hk hsizes d := by
  unfold _root_.GD.N0232.N0719.N0815.d010940
  apply le_antisymm
  · exact iInf_le_of_le 0 <|
      (_root_.GD.N0232.N0719.N0815.d010943 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0815.d010938 0) (_root_.GD.N0232.N0719.N0815.d010939 0) d).le
  · apply le_iInf
    intro n
    rw [_root_.GD.N0232.N0719.N0815.d010943 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0815.d010938 n) (_root_.GD.N0232.N0719.N0815.d010939 n) d]


theorem d010945
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    {e d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ}
    (hed : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) :
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active e ≤
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d := by
  unfold _root_.GD.N0232.N0719.N0815.d010940
  exact iInf_mono fun n ↦
    _root_.GD.N0232.N0719.N0815.d010936
      k sizes hk hsizes active (_root_.GD.N0232.N0719.N0815.d010938 n) hed


theorem d010946
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) =
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d := by
  unfold _root_.GD.N0232.N0719.N0815.d010940
  congr 1
  funext n
  exact _root_.GD.N0232.N0719.N0815.d010937
    k sizes hk hsizes active (_root_.GD.N0232.N0719.N0815.d010938 n)
      shift dilation hdilation d hd



theorem d010947
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active d ≤
      _root_.GD.N0232.N0719.N0815.d010941 k sizes hk hsizes d := by
  unfold _root_.GD.N0232.N0719.N0815.d010940
  apply iInf_le_of_le 0
  unfold _root_.GD.N0232.N0719.N0815.d010935 _root_.GD.N0232.N0719.N0815.d010941
  apply iSup_le
  intro theta
  exact le_iSup
    (fun eta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
      _root_.GD.N0232.N0719.N0815.d010933 k sizes hk hsizes eta d) theta.1



def d010948
    (r k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ENNReal :=
  ⨆ active : {active : Finset (Fin k) // active.card ≤ r},
    _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active.1 d



theorem d010949
    (r k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {e d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ}
    (hed : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) :
    _root_.GD.N0232.N0719.N0815.d010948 r k sizes hk hsizes e ≤
      _root_.GD.N0232.N0719.N0815.d010948 r k sizes hk hsizes d := by
  unfold _root_.GD.N0232.N0719.N0815.d010948
  apply iSup_mono
  intro active
  exact _root_.GD.N0232.N0719.N0815.d010945
    k sizes hk hsizes active.1 hed


theorem d010950
    (r k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0815.d010948 r k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) =
      _root_.GD.N0232.N0719.N0815.d010948 r k sizes hk hsizes d := by
  unfold _root_.GD.N0232.N0719.N0815.d010948
  congr 1
  funext active
  exact _root_.GD.N0232.N0719.N0815.d010946
    k sizes hk hsizes active.1 shift dilation hdilation d hd



theorem d010951
    {r s : ℕ} (hrs : r ≤ s)
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0815.d010948 r k sizes hk hsizes d ≤
      _root_.GD.N0232.N0719.N0815.d010948 s k sizes hk hsizes d := by
  unfold _root_.GD.N0232.N0719.N0815.d010948
  apply iSup_le
  intro active
  exact le_iSup
    (fun face : {face : Finset (Fin k) // face.card ≤ s} ↦
      _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes face.1 d)
    ⟨active.1, active.2.trans hrs⟩




theorem d010952
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0815.d010948 k k sizes hk hsizes d =
      _root_.GD.N0232.N0719.N0815.d010941 k sizes hk hsizes d := by
  apply le_antisymm
  · unfold _root_.GD.N0232.N0719.N0815.d010948
    apply iSup_le
    intro active
    exact _root_.GD.N0232.N0719.N0815.d010947
      k sizes hk hsizes active.1 d
  · rw [← _root_.GD.N0232.N0719.N0815.d010944 k sizes hk hsizes d]
    exact le_iSup
      (fun active : {active : Finset (Fin k) // active.card ≤ k} ↦
        _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes active.1 d)
      ⟨Finset.univ, by simp⟩



def d010953
    {n : ℕ}
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (faces : Fin n → Finset (Fin k))
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (i : Fin n) : ENNReal :=
  _root_.GD.N0232.N0719.N0815.d010940 k sizes hk hsizes (faces i) d



theorem d010954
    {n : ℕ}
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (faces : Fin n → Finset (Fin k))
    {e d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ}
    (hed : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) :
    ∀ i, _root_.GD.N0232.N0719.N0815.d010953 k sizes hk hsizes faces e i ≤
      _root_.GD.N0232.N0719.N0815.d010953 k sizes hk hsizes faces d i := by
  intro i
  exact _root_.GD.N0232.N0719.N0815.d010945
    k sizes hk hsizes (faces i) hed



theorem d010955
    {n : ℕ}
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (faces : Fin n → Finset (Fin k))
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    ∀ i,
      _root_.GD.N0232.N0719.N0815.d010953 k sizes hk hsizes faces
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) i =
        _root_.GD.N0232.N0719.N0815.d010953 k sizes hk hsizes faces d i := by
  intro i
  exact _root_.GD.N0232.N0719.N0815.d010946
    k sizes hk hsizes (faces i) shift dilation hdilation d hd




abbrev d010956
    (k : ℕ) (sizes : Fin k → ℕ) :=
  {d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ // Measurable d}


def d010957
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.N0815.d010956 k sizes) : ENNReal :=
  _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d.1


def d010958
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    Set (_root_.GD.N0232.N0719.N0815.d010956 k sizes) :=
  {d | _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes d.1}



theorem d010959
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0616.d000721
      (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d)
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) := by
  intro d e hd he
  intro theta
  exact (he theta).trans (hd theta)


def d010960
    {n : ℕ}
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (faces : Fin n → Finset (Fin k))
    (i : Fin n) (d : _root_.GD.N0232.N0719.N0815.d010956 k sizes) : ENNReal :=
  _root_.GD.N0232.N0719.N0815.d010953 k sizes hk hsizes faces d.1 i



theorem d010961
    {n : ℕ}
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (faces : Fin n → Finset (Fin k)) :
    _root_.GD.N0230.N0616.d000724
      (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d)
      (_root_.GD.N0232.N0719.N0815.d010960 k sizes hk hsizes faces) := by
  intro i e d hed
  exact _root_.GD.N0232.N0719.N0815.d010954
    k sizes hk hsizes faces (fun theta ↦ hed theta) i


def d010962
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ)
    (d : _root_.GD.N0232.N0719.N0815.d010956 k sizes) :
    _root_.GD.N0232.N0719.N0815.d010956 k sizes :=
  ⟨_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d.1,
    _root_.GD.N0232.N0719.N0842.d010912 k sizes shift dilation d.1 d.2⟩















theorem d010963
    {n : ℕ}
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (faces : Fin n → Finset (Fin k))
    (p : _root_.GD.N0232.N0719.N0815.d010956 k sizes)
    (hlex : _root_.GD.N0230.N0616.d000722
      (_root_.GD.N0232.N0719.N0815.d010960 k sizes hk hsizes faces)
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p)
    (hfaithful : _root_.GD.N0230.N0616.d000723
      (_root_.GD.N0232.N0719.N0815.d010960 k sizes hk hsizes faces)
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p) :
    (∀ (shift dilation : ℝ) (hdilation : 0 < dilation),
        _root_.GD.N0232.N0719.N0815.d010962 k sizes shift dilation p = p) ∧
      _root_.GD.N0230.N0608.d000674
        (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d) p := by
  constructor
  · intro shift dilation hdilation
    apply hfaithful
      (_root_.GD.N0232.N0719.N0815.d010962 k sizes shift dilation p)
    · exact (_root_.GD.N0232.N0719.N0842.d010923
        k sizes hk hsizes shift dilation hdilation p.1 p.2).2 hlex.1
    · intro i
      exact _root_.GD.N0232.N0719.N0815.d010955
        k sizes hk hsizes faces shift dilation hdilation p.1 p.2 i
  · exact _root_.GD.N0230.N0616.d000725
      (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d)
      (_root_.GD.N0232.N0719.N0815.d010960 k sizes hk hsizes faces)
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p
      (_root_.GD.N0232.N0719.N0815.d010959 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0815.d010961
        k sizes hk hsizes faces)
      hlex hfaithful

end

end N0815
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0815.d010931
#print axioms _root_.GD.N0232.N0719.N0815.d010934
#print axioms _root_.GD.N0232.N0719.N0815.d010936
#print axioms _root_.GD.N0232.N0719.N0815.d010937
#print axioms _root_.GD.N0232.N0719.N0815.d010945
#print axioms _root_.GD.N0232.N0719.N0815.d010946
#print axioms _root_.GD.N0232.N0719.N0815.d010944
#print axioms _root_.GD.N0232.N0719.N0815.d010949
#print axioms _root_.GD.N0232.N0719.N0815.d010950
#print axioms _root_.GD.N0232.N0719.N0815.d010951
#print axioms _root_.GD.N0232.N0719.N0815.d010952
#print axioms _root_.GD.N0232.N0719.N0815.d010954
#print axioms _root_.GD.N0232.N0719.N0815.d010955
#print axioms _root_.GD.N0232.N0719.N0815.d010959
#print axioms _root_.GD.N0232.N0719.N0815.d010961
#print axioms _root_.GD.N0232.N0719.N0815.d010963
