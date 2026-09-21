import GD.Module0728
import GD.Module0060






















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0809

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0596



abbrev d010964 (k : ℕ) := Finset (Fin k) × ℕ



def d010965
    {k : ℕ} (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k) : Prop :=
  Function.Surjective schedule



noncomputable def d010966 (k : ℕ) : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k :=
  (exists_surjective_nat (_root_.GD.N0232.N0719.N0809.d010964 k)).choose

theorem d010967 (k : ℕ) :
    _root_.GD.N0232.N0719.N0809.d010965 (_root_.GD.N0232.N0719.N0809.d010966 k) :=
  (exists_surjective_nat (_root_.GD.N0232.N0719.N0809.d010964 k)).choose_spec


def d010968
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (stage : ℕ) (d : _root_.GD.N0232.N0719.N0815.d010956 k sizes) : ENNReal :=
  _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes
    (schedule stage).1 (_root_.GD.N0232.N0719.N0815.d010938 (schedule stage).2) d.1



theorem d010969
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k) :
    _root_.GD.N0230.N0596.d000732
      (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d)
      (_root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes schedule) := by
  intro stage e d hed
  exact _root_.GD.N0232.N0719.N0815.d010936 k sizes hk hsizes
    (schedule stage).1 (_root_.GD.N0232.N0719.N0815.d010938 (schedule stage).2)
      (fun theta ↦ hed theta)


theorem d010970
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (stage : ℕ)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.N0815.d010956 k sizes) :
    _root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes schedule stage
        (_root_.GD.N0232.N0719.N0815.d010962 k sizes shift dilation d) =
      _root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes schedule stage d := by
  exact _root_.GD.N0232.N0719.N0815.d010937 k sizes hk hsizes
    (schedule stage).1 (_root_.GD.N0232.N0719.N0815.d010938 (schedule stage).2)
      shift dilation hdilation d.1 d.2


def d010971
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (C : Set (_root_.GD.N0232.N0719.N0815.d010956 k sizes))
    (p : _root_.GD.N0232.N0719.N0815.d010956 k sizes) : Prop :=
  ∀ d, d ∈ C →
    (∀ (active : Finset (Fin k)) (depth : ℕ),
      _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active (_root_.GD.N0232.N0719.N0815.d010938 depth) d.1 =
        _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active (_root_.GD.N0232.N0719.N0815.d010938 depth) p.1) →
    d = p



theorem d010972
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (C : Set (_root_.GD.N0232.N0719.N0815.d010956 k sizes))
    (p : _root_.GD.N0232.N0719.N0815.d010956 k sizes)
    (hfaithful : _root_.GD.N0232.N0719.N0809.d010971
      k sizes hk hsizes C p) :
    _root_.GD.N0230.N0596.d000731
      (_root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes schedule) C p := by
  intro d hd hall
  apply hfaithful d hd
  intro active depth
  obtain ⟨stage, hstage⟩ := hschedule (active, depth)
  have h := hall stage
  simpa [_root_.GD.N0232.N0719.N0809.d010968, hstage] using h







theorem d010973
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (p : _root_.GD.N0232.N0719.N0815.d010956 k sizes)
    (hlex : _root_.GD.N0230.N0596.d000730
      (_root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes schedule)
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p)
    (hfaithful : _root_.GD.N0232.N0719.N0809.d010971 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p) :
    (∀ (shift dilation : ℝ) (hdilation : 0 < dilation),
        _root_.GD.N0232.N0719.N0815.d010962 k sizes shift dilation p = p) ∧
      _root_.GD.N0230.N0608.d000674
        (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d) p := by
  have hsequenceFaithful : _root_.GD.N0230.N0596.d000731
      (_root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes schedule)
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p :=
    _root_.GD.N0232.N0719.N0809.d010972
      k sizes hk hsizes schedule hschedule
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p hfaithful
  constructor
  · intro shift dilation hdilation
    apply hsequenceFaithful
      (_root_.GD.N0232.N0719.N0815.d010962 k sizes shift dilation p)
    · exact (_root_.GD.N0232.N0719.N0842.d010923
        k sizes hk hsizes shift dilation hdilation p.1 p.2).2 hlex.1
    · intro stage
      exact _root_.GD.N0232.N0719.N0809.d010970
        k sizes hk hsizes schedule stage shift dilation hdilation p
  · exact _root_.GD.N0230.N0596.d000733
      (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d)
      (_root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes schedule)
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p
      (_root_.GD.N0232.N0719.N0815.d010959 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0809.d010969
        k sizes hk hsizes schedule)
      hlex hsequenceFaithful



theorem d010974
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (p : _root_.GD.N0232.N0719.N0815.d010956 k sizes)
    (hlex : _root_.GD.N0230.N0596.d000730
      (_root_.GD.N0232.N0719.N0809.d010968 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0809.d010966 k))
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p)
    (hfaithful : _root_.GD.N0232.N0719.N0809.d010971 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0815.d010958 k sizes hk hsizes) p) :
    (∀ (shift dilation : ℝ) (hdilation : 0 < dilation),
        _root_.GD.N0232.N0719.N0815.d010962 k sizes shift dilation p = p) ∧
      _root_.GD.N0230.N0608.d000674
        (fun theta d ↦ _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d) p := by
  exact _root_.GD.N0232.N0719.N0809.d010973
    k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k)
      (_root_.GD.N0232.N0719.N0809.d010967 k) p hlex hfaithful

end

end N0809
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0809.d010969
#print axioms _root_.GD.N0232.N0719.N0809.d010970
#print axioms _root_.GD.N0232.N0719.N0809.d010967
#print axioms _root_.GD.N0232.N0719.N0809.d010972
#print axioms _root_.GD.N0232.N0719.N0809.d010973
#print axioms _root_.GD.N0232.N0719.N0809.d010974
