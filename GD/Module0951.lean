import GD.Module0304
import GD.Module0635
import GD.Module0949
import GD.Module0326



















open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Topology

namespace GD
namespace N0232
namespace N0720
namespace N1261

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0571
open _root_.GD.N0230.N0676
open _root_.GD.N0230.N0677
open _root_.GD.N0230.N0559
open _root_.GD.N0238.N0757
open _root_.GD.N0238
open _root_.GD.N0232.N0719.N0945
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

abbrev d014926 := _root_.GD.N0232.N0720.N1025.d014304 m n hm hn

abbrev d014927 := _root_.GD.N0232.N0720.N1025.d014302 m n


@[reducible] noncomputable local instance d014928 :
    MulAction _root_.GD.N0232.N0720.N1025.d014301 _root_.GD.N0232.N0720.N1080.d014168 where
  smul := _root_.GD.N0232.N0720.N1215.d014272
  one_smul := _root_.GD.N0232.N0720.N1215.d014276
  mul_smul g h theta := (_root_.GD.N0232.N0720.N1215.d014278 g h theta).symm



@[reducible] noncomputable local instance d014929 :
    MulAction _root_.GD.N0232.N0720.N1025.d014301 (_root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :=
  _root_.GD.N0232.N0720.N1215.d014916 m n hm hn

noncomputable local instance d014930 :
    MeasurableSpace.CountablyGenerated (_root_.GD.N0232.N0720.N1080.d014170 m n) := by
  infer_instance

noncomputable local instance d014931 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

noncomputable local instance d014932 :
    SFinite (_root_.GD.N0232.N0720.N1080.d014172 m n) := inferInstance

noncomputable local instance d014933 :
    IsSeparable (_root_.GD.N0232.N0720.N1080.d014172 m n) := inferInstance

noncomputable local instance d014934 :
    Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

noncomputable local instance d014935 :
    SecondCountableTopology (_root_.GD.N0232.N0720.N1261.d014927 m n) := inferInstance

noncomputable local instance d014936 :
    TopologicalSpace.SeparableSpace (_root_.GD.N0232.N0720.N1261.d014927 m n) :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

private theorem d014937 (j : ℕ) :
    0 < (1 + _root_.GD.N0232.N0720.N1080.d014248 m n hm hn) *
      (1 + ‖TopologicalSpace.denseSeq (_root_.GD.N0232.N0720.N1261.d014927 m n) j‖) := by
  exact mul_pos (by
    have := norm_nonneg (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
    simpa [_root_.GD.N0232.N0720.N1080.d014248] using add_pos_of_pos_of_nonneg zero_lt_one this)
    (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _))



def d014938 (j : ℕ) (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) : ℝ :=
  inner ℝ (TopologicalSpace.denseSeq (_root_.GD.N0232.N0720.N1261.d014927 m n) j)
      ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).symm p.1) /
    ((1 + _root_.GD.N0232.N0720.N1080.d014248 m n hm hn) *
      (1 + ‖TopologicalSpace.denseSeq (_root_.GD.N0232.N0720.N1261.d014927 m n) j‖))


theorem d014939 (j : ℕ) :
    Continuous (_root_.GD.N0232.N0720.N1261.d014938 m n hm hn j) := by
  let probe : _root_.GD.N0232.N0720.N1261.d014927 m n := TopologicalSpace.denseSeq (_root_.GD.N0232.N0720.N1261.d014927 m n) j
  have hpair : Continuous (fun x : WeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n) ↦
      inner ℝ probe ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).symm x)) := by
    exact WeakBilin.eval_continuous
      (topDualPairing ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).flip
      (InnerProductSpace.toDual ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n) probe)
  exact ((hpair.comp continuous_subtype_val).div_const
    ((1 + _root_.GD.N0232.N0720.N1080.d014248 m n hm hn) * (1 + ‖probe‖)))


theorem d014940
    {p q : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn}
    (htrace : ∀ j, _root_.GD.N0232.N0720.N1261.d014938 m n hm hn j p = _root_.GD.N0232.N0720.N1261.d014938 m n hm hn j q) :
    p = q := by
  apply Subtype.ext
  apply (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).symm.injective
  apply (TopologicalSpace.denseRange_denseSeq (_root_.GD.N0232.N0720.N1261.d014927 m n)).eq_of_inner_right ℝ
  intro j
  have hj := htrace j
  unfold _root_.GD.N0232.N0720.N1261.d014938 at hj
  exact (div_left_inj' (_root_.GD.N0232.N0720.N1261.d014937 m n hm hn j).ne').mp hj


theorem d014941 :
    Pairwise fun p q : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn ↦
      ∃ j, _root_.GD.N0232.N0720.N1261.d014938 m n hm hn j p ≠ _root_.GD.N0232.N0720.N1261.d014938 m n hm hn j q := by
  intro p q hpq
  contrapose! hpq
  exact _root_.GD.N0232.N0720.N1261.d014940 m n hm hn hpq

noncomputable local instance d014942 :
    CompactSpace (_root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :=
  isCompact_iff_compactSpace.mp (_root_.GD.N0232.N0720.N1025.d014311 m n hm hn)




noncomputable instance d014943 :
    TopologicalSpace.MetrizableSpace (_root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :=
  Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun j p ↦ _root_.GD.N0232.N0720.N1261.d014938 m n hm hn j p)
    (_root_.GD.N0232.N0720.N1261.d014939 m n hm hn)
    (_root_.GD.N0232.N0720.N1261.d014941 m n hm hn)



noncomputable instance d014944 : MetricSpace (_root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :=
  TopologicalSpace.metrizableSpaceMetric (_root_.GD.N0232.N0720.N1261.d014926 m n hm hn)


def d014945
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) : ℝ :=
  dist (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p) p ^ 2

theorem d014946
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :
    0 ≤ _root_.GD.N0232.N0720.N1261.d014945 m n hm hn g p :=
  sq_nonneg _

theorem d014947
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :
    _root_.GD.N0232.N0720.N1261.d014945 m n hm hn g p = 0 ↔
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p := by
  simp [_root_.GD.N0232.N0720.N1261.d014945]

theorem d014948 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Continuous (_root_.GD.N0232.N0720.N1261.d014945 m n hm hn g) := by
  unfold _root_.GD.N0232.N0720.N1261.d014945
  exact (continuous_dist.comp
    ((_root_.GD.N0232.N0720.N1483.d014904 m n hm hn g).prodMk continuous_id)).pow 2


def d014949 (theta : _root_.GD.N0232.N0720.N1080.d014168) (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) : ENNReal :=
  _root_.GD.N0232.N0720.N1025.d014305 m n theta p.1


def d014950 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ENNReal :=
  _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)


def d014951 (g : _root_.GD.N0232.N0720.N1025.d014301) : ENNReal :=
  ENNReal.ofReal (g.d009239 ^ 2)


theorem d014952 :
    _root_.GD.N0230.N0676.d000914
      (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) (_root_.GD.N0232.N0720.N1261.d014951) := by
  intro g theta p
  change _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
      (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).2) =
    ENNReal.ofReal (g.d009239 ^ 2) *
      _root_.GD.N0232.N0720.N1080.d014182 m n theta ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).symm p.1)
  exact _root_.GD.N0232.N0720.N1215.d014290 m n hm hn g theta
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).2


theorem d014953 :
    _root_.GD.N0230.N0676.d000915
      (_root_.GD.N0232.N0720.N1261.d014950 m n hm hn) _root_.GD.N0232.N0720.N1261.d014951 := by
  intro g theta
  exact _root_.GD.N0232.N0720.N1215.d014296 m n hm hn g theta



theorem d014954 (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :
    _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) (_root_.GD.N0232.N0720.N1261.d014950 m n hm hn) p := by
  intro theta
  exact ((_root_.GD.N0232.N0720.N1025.d014306 m n hm hn p.1).1 p.2) theta



theorem d014955 (e d : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) e d ↔
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e.1 d.1 :=
  Iff.rfl





theorem d014956 (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) p ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) p.1 := by
  constructor
  · intro hp e he
    have heMem : e ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      _root_.GD.N0232.N0720.N1025.d014314 m n hm hn p.2 he
    have heq : (⟨e, heMem⟩ : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) = p := hp ⟨e, heMem⟩ he
    exact congrArg Subtype.val heq
  · intro hp e he
    apply Subtype.ext
    exact hp e.1 he



theorem d014957 (p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) p ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).symm p.1) := by
  exact (_root_.GD.N0232.N0720.N1261.d014956 m n hm hn p).trans
    (_root_.GD.N0232.N0720.N1025.d014315 m n p.1)



abbrev d014958 := _root_.GD.N0230.N0677.d004383
  (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) (_root_.GD.N0232.N0720.N1261.d014950 m n hm hn)


def d014959 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d : _root_.GD.N0232.N0720.N1261.d014958 m n hm hn) : _root_.GD.N0232.N0720.N1261.d014958 m n hm hn :=
  _root_.GD.N0230.N0677.d004384
    (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) (_root_.GD.N0232.N0720.N1261.d014950 m n hm hn) _root_.GD.N0232.N0720.N1261.d014951
    (_root_.GD.N0232.N0720.N1261.d014952 m n hm hn)
    (_root_.GD.N0232.N0720.N1261.d014953 m n hm hn) g d

@[simp] theorem d014960 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d : _root_.GD.N0232.N0720.N1261.d014958 m n hm hn) :
    (_root_.GD.N0232.N0720.N1261.d014959 m n hm hn g d : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn) =
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g d.1 :=
  rfl








theorem d014961
    (hparameter : ∀ d : _root_.GD.N0232.N0720.N1261.d014958 m n hm hn,
      Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦
        _root_.GD.N0232.N0720.N1261.d014959 m n hm hn g d))
    (stage : ℕ → Finset _root_.GD.N0232.N0719.N0945.d009269)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (energy : _root_.GD.N0232.N0719.N0945.d009269 →
      _root_.GD.N0232.N0720.N1261.d014958 m n hm hn → ℝ)
    (point : ℕ → _root_.GD.N0232.N0720.N1261.d014958 m n hm hn)
    (henergy : ∀ N, ∀ i ∈ stage N,
      dist
          (_root_.GD.N0232.N0720.N1261.d014959 m n hm hn (_root_.GD.N0232.N0719.N0945.d009270 i) (point N))
          (point N) ^ 2 ≤
        energy i (point N))
    (hvanish : _root_.GD.N0230.N0559.d004363 stage energy point)
    (control : _root_.GD.N0232.N0720.N1261.d014958 m n hm hn → ℝ)
    (hcompact : _root_.GD.N0238.d004342 control)
    (hbounded : _root_.GD.N0238.d004344 control point) :
    ∃ p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn,
      _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) (_root_.GD.N0232.N0720.N1261.d014950 m n hm hn) p ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).symm p.1) ∧
      ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p := by
  have hstate : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      Continuous (_root_.GD.N0232.N0720.N1261.d014959 m n hm hn g) := by
    intro g
    apply Continuous.subtype_mk
    exact (_root_.GD.N0232.N0720.N1483.d014904 m n hm hn g).comp
      continuous_subtype_val
  obtain ⟨p, hpFeasible, hpTerminal, hpFixed⟩ :=
    _root_.GD.N0230.N0677.d004386
      (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) (_root_.GD.N0232.N0720.N1261.d014950 m n hm hn) _root_.GD.N0232.N0720.N1261.d014951
      (_root_.GD.N0232.N0720.N1261.d014952 m n hm hn)
      (_root_.GD.N0232.N0720.N1261.d014953 m n hm hn)
      _root_.GD.N0232.N0719.N0945.d009270 _root_.GD.N0232.N0719.N0945.d009271 hstate hparameter stage hstage hmono energy point
      henergy hvanish control hcompact hbounded
  refine ⟨p, hpFeasible,
    (_root_.GD.N0232.N0720.N1261.d014957 m n hm hn p).1 hpTerminal,
    ?_⟩
  intro g
  exact hpFixed g

end

end N1261
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1261.d014943
#print axioms _root_.GD.N0232.N0720.N1261.d014957
#print axioms _root_.GD.N0232.N0720.N1261.d014961
