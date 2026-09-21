import GD.Module1066
import GD.Module1070










































open MeasureTheory Set
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1129

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1159




def d017182
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (i : Fin candidate.width) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i)
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal -
    (_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i) s.value).toReal


def d017183
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (i : Fin candidate.width) : ℝ :=
  _root_.GD.N0232.N0720.N1128.d017098 m n (candidate.packet i)
    (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value







def d017184
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (lambda : ℝ) : ℝ :=
  ∑ i, candidate.weight i *
    (lambda * _root_.GD.N0232.N0720.N1129.d017183 m n s candidate i -
      _root_.GD.N0232.N0720.N1129.d017182 m n s candidate i)

theorem d017185
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (lambda : ℝ)
    (hcertificate : _root_.GD.N0232.N0720.N1128.d017105
      m n s candidate lambda) :
    0 ≤ _root_.GD.N0232.N0720.N1129.d017184
      m n s candidate lambda := by
  unfold _root_.GD.N0232.N0720.N1129.d017184
    _root_.GD.N0232.N0720.N1129.d017183 _root_.GD.N0232.N0720.N1129.d017182
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (candidate.weight_nonneg i)
  exact sub_nonneg.mpr (hcertificate.2 (candidate.packet i))





theorem d017186
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate
        (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate) =
      lambda ^ 2 *
        _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value := by
  have hrepair :
      (fun omega ↦
        _root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate omega) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦
          (1 - lambda) * _root_.GD.N0232.N0720.N1130.d017075 m n candidate omega +
            lambda * s.value omega := by
    simpa only [_root_.GD.N0232.N0720.N1128.d017104, _root_.GD.N0232.N0720.N1080.d014172] using
      _root_.GD.N0232.N0720.N1128.d017095 m n lambda
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value _root_.GD.N0232.N0720.N1080.d014169
  have hcompletion :
      (fun omega ↦ _root_.GD.N0232.N0720.N1130.d017075 m n candidate omega) =ᵐ[
        _root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight := by
    simpa only [_root_.GD.N0232.N0720.N1130.d017075] using
      (_root_.GD.N0232.N0720.N1126.d016427
        (m := m) (n := n) candidate.packet candidate.weight
          candidate.weight_nonneg)
  unfold _root_.GD.N0232.N0720.N1131.d017154
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hrepair, hcompletion] with omega hrepairOmega hcompletionOmega
  rw [hrepairOmega, hcompletionOmega]
  ring



def d017187
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  ‖s.value‖ ^ 2 -
    _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight



theorem d017188
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value =
      _root_.GD.N0232.N0720.N1129.d017187 m n s candidate := by
  have hself : s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
    intro theta
    exact le_rfl
  have hexact := _root_.GD.N0232.N0720.N1131.d017159
    m n s candidate s.value hself
  unfold _root_.GD.N0232.N0720.N1129.d017187
  simpa [_root_.GD.N0232.N0720.N1131.d017153] using hexact.symm

theorem d017189
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1129.d017187 m n s candidate := by
  rw [← _root_.GD.N0232.N0720.N1129.d017188]
  exact _root_.GD.N0232.N0720.N1131.d017156 m n candidate s.value





theorem d017190
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017153 m n s candidate
        (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate) =
      (1 - lambda) *
        _root_.GD.N0232.N0720.N1129.d017184 m n s candidate lambda := by
  unfold _root_.GD.N0232.N0720.N1131.d017153
    _root_.GD.N0232.N0720.N1129.d017184
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hidentity := _root_.GD.N0232.N0720.N1128.d017107
    m n lambda s candidate (candidate.packet i)
  have hidentity' :
      (_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i)
          (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate)).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i) s.value).toReal =
        (1 - lambda) *
          (_root_.GD.N0232.N0720.N1129.d017182 m n s candidate i -
            lambda * _root_.GD.N0232.N0720.N1129.d017183 m n s candidate i) := by
    simpa only [_root_.GD.N0232.N0720.N1129.d017182,
      _root_.GD.N0232.N0720.N1129.d017183] using hidentity
  calc
    candidate.weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i) s.value).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i)
            (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate)).toReal) =
      candidate.weight i *
        (-((_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i)
              (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate)).toReal -
            (_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i) s.value).toReal)) := by ring
    _ = candidate.weight i *
        (-((1 - lambda) *
          (_root_.GD.N0232.N0720.N1129.d017182 m n s candidate i -
            lambda * _root_.GD.N0232.N0720.N1129.d017183
              m n s candidate i))) := by rw [hidentity']
    _ = (1 - lambda) *
        (candidate.weight i *
          (lambda * _root_.GD.N0232.N0720.N1129.d017183 m n s candidate i -
            _root_.GD.N0232.N0720.N1129.d017182 m n s candidate i)) := by ring













def d017191
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (lambda : ℝ) : ℝ :=
  lambda ^ 2 * _root_.GD.N0232.N0720.N1129.d017187 m n s candidate +
    (1 - lambda) *
      _root_.GD.N0232.N0720.N1129.d017184 m n s candidate lambda +
    _root_.GD.N0232.N0720.N1130.d017078 m n candidate +
    _root_.GD.N0232.N0720.N1130.d017079 m n candidate



theorem d017192
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017163 m n s candidate
        (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate) =
      _root_.GD.N0232.N0720.N1129.d017191
        m n s candidate lambda := by
  unfold _root_.GD.N0232.N0720.N1131.d017163
    _root_.GD.N0232.N0720.N1129.d017191
  rw [_root_.GD.N0232.N0720.N1129.d017186,
    _root_.GD.N0232.N0720.N1129.d017188,
    _root_.GD.N0232.N0720.N1129.d017190]


theorem d017193
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (lambda : ℝ)
    (hcertificate : _root_.GD.N0232.N0720.N1128.d017105
      m n s candidate lambda) :
    0 ≤ _root_.GD.N0232.N0720.N1129.d017191
      m n s candidate lambda := by
  rw [← _root_.GD.N0232.N0720.N1129.d017192]
  exact _root_.GD.N0232.N0720.N1131.d017166
    m n s candidate (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate)
      (_root_.GD.N0232.N0720.N1128.d017108
        m n lambda s candidate hcertificate)



theorem d017194
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1129.d017191 m n s candidate 0 =
      _root_.GD.N0232.N0720.N1129.d017184 m n s candidate 0 +
        _root_.GD.N0232.N0720.N1130.d017078 m n candidate +
        _root_.GD.N0232.N0720.N1130.d017079 m n candidate := by
  simp [_root_.GD.N0232.N0720.N1129.d017191]



theorem d017195
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1129.d017191 m n s candidate 1 =
      _root_.GD.N0232.N0720.N1129.d017187 m n s candidate +
        _root_.GD.N0232.N0720.N1130.d017078 m n candidate +
        _root_.GD.N0232.N0720.N1130.d017079 m n candidate := by
  simp [_root_.GD.N0232.N0720.N1129.d017191]






def d017196
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (candidate : _root_.GD.N0232.N0720.N1130.d017074) (lambda : ℝ),
      _root_.GD.N0232.N0720.N1128.d017105 m n s candidate lambda ∧
        _root_.GD.N0232.N0720.N1129.d017191
          m n s candidate lambda < epsilon



theorem d017197
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : _root_.GD.N0232.N0720.N1129.d017196
      m n s) :
    _root_.GD.N0232.N0720.N1131.d017168 m n s := by
  intro epsilon hepsilon
  obtain ⟨candidate, lambda, hcertificate, hmerit⟩ :=
    hsmall epsilon hepsilon
  refine ⟨candidate,
    _root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1128.d017108
      m n lambda s candidate hcertificate
  · rw [_root_.GD.N0232.N0720.N1129.d017192]
    exact hmerit




theorem d017198
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hsmall : _root_.GD.N0232.N0720.N1129.d017196
      m n s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact
    _root_.GD.N0232.N0720.N1131.d017169
      m n hm hn s hstrict
        (_root_.GD.N0232.N0720.N1129.d017197
          m n s hsmall)

end
end N1129
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1129.d017186
#print axioms _root_.GD.N0232.N0720.N1129.d017190
#print axioms _root_.GD.N0232.N0720.N1129.d017192
#print axioms _root_.GD.N0232.N0720.N1129.d017198
