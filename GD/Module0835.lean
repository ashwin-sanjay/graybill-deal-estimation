import GD.Module0834
import GD.Module0622










open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137



theorem d012748
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q)
    {B : ℝ} (hB : 0 ≤ B) (hqBound : ∀ p, |q p| ≤ B) :
    MemLp
        (fun ω =>
          _root_.GD.N0107.d009038 m n μ σ τ
              (_root_.GD.N0107.d009046 m n σ τ)
              (_root_.GD.N0107.d009045 m n σ τ) ω *
            (_root_.GD.N0107.d009039 m n μ σ τ
                (_root_.GD.N0107.d009046 m n σ τ) ω -
              _root_.GD.N0107.d009046 m n σ τ))
        2 (_root_.GD.N0107.d009030 m n μ σ τ)
      ∧
    MemLp
        (fun ω =>
          _root_.GD.N0107.d009038 m n μ σ τ
              (_root_.GD.N0107.d009046 m n σ τ)
              (_root_.GD.N0107.d009045 m n σ τ) ω *
            q
              (_root_.GD.N0107.d009039 m n μ σ τ
                  (_root_.GD.N0107.d009046 m n σ τ) ω,
                _root_.GD.N0107.d009040 m n μ σ τ
                  (_root_.GD.N0107.d009046 m n σ τ) ω))
        2 (_root_.GD.N0107.d009030 m n μ σ τ) := by
  let e := _root_.GD.N0107.d009046 m n σ τ
  let Sigma := _root_.GD.N0107.d009045 m n σ τ
  have he0 : 0 < e :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hσ hτ
  have he1 : e < 1 :=
    _root_.GD.N0107.d009051 (by omega) (by omega) hσ hτ
  have hcanonical :=
    _root_.GD.N0119.d009082
      m n hm hn he0 he1 q hq hB hqBound
      (Sigma := Sigma)
  have hmap :=
    _root_.GD.N0107.d009031
      m n μ σ τ hσ.ne' hτ.ne'
  constructor
  · have hpull :=
      _root_.GD.N0107.d012743
        (P := _root_.GD.N0107.d009030 m n μ σ τ)
        (Q := _root_.GD.N0137.d008914 m n)
        (S := _root_.GD.N0107.d009025 m n μ σ τ)
        (f := fun z =>
          _root_.GD.N0137.d008942 m n e Sigma z * (_root_.GD.N0137.d008943 m n e z - e))
        (p := 2)
        (_root_.GD.N0107.d009027 m n μ σ τ)
        (by
          exact ((_root_.GD.N0137.d008946 m n e Sigma).fst.mul
            ((_root_.GD.N0137.d008946 m n e Sigma).snd.fst.sub
              measurable_const)))
        hmap hcanonical.1
    change MemLp
      (fun ω =>
        _root_.GD.N0137.d008942 m n e Sigma
            (_root_.GD.N0107.d009025 m n μ σ τ ω) *
          (_root_.GD.N0137.d008943 m n e
              (_root_.GD.N0107.d009025 m n μ σ τ ω) - e))
      2 (_root_.GD.N0107.d009030 m n μ σ τ) at hpull
    simpa [_root_.GD.N0107.d009038, _root_.GD.N0107.d009039,
      Function.comp_apply, e, Sigma] using hpull
  · have hpull :=
      _root_.GD.N0107.d012743
        (P := _root_.GD.N0107.d009030 m n μ σ τ)
        (Q := _root_.GD.N0137.d008914 m n)
        (S := _root_.GD.N0107.d009025 m n μ σ τ)
        (f := fun z =>
          _root_.GD.N0137.d008942 m n e Sigma z *
            q (_root_.GD.N0137.d008943 m n e z, _root_.GD.N0137.d008944 m n e z))
        (p := 2)
        (_root_.GD.N0107.d009027 m n μ σ τ)
        (by
          exact (_root_.GD.N0137.d008946 m n e Sigma).fst.mul
            (hq.comp
              ((_root_.GD.N0137.d008946 m n e Sigma).snd.fst.prodMk
                (_root_.GD.N0137.d008946 m n e Sigma).snd.snd)))
        hmap hcanonical.2
    change MemLp
      (fun ω =>
        _root_.GD.N0137.d008942 m n e Sigma
            (_root_.GD.N0107.d009025 m n μ σ τ ω) *
          q
            (_root_.GD.N0137.d008943 m n e
                (_root_.GD.N0107.d009025 m n μ σ τ ω),
              _root_.GD.N0137.d008944 m n e
                (_root_.GD.N0107.d009025 m n μ σ τ ω)))
      2 (_root_.GD.N0107.d009030 m n μ σ τ) at hpull
    simpa [_root_.GD.N0107.d009038, _root_.GD.N0107.d009039, _root_.GD.N0107.d009040,
      Function.comp_apply, e, Sigma] using hpull


theorem d012749
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q)
    {B : ℝ} (hB : 0 ≤ B) (hqBound : ∀ p, |q p| ≤ B) :
    MemLp
        (fun ω =>
          _root_.GD.N0107.d009090 m n ω *
            (_root_.GD.N0107.d009091 m n
                (_root_.GD.N0107.d009085 ω.1)
                (_root_.GD.N0107.d009085 ω.2) -
              _root_.GD.N0107.d009046 m n σ τ))
        2 (_root_.GD.N0107.d009030 m n μ σ τ)
      ∧
    MemLp
        (fun ω =>
          _root_.GD.N0107.d009090 m n ω *
            q
              (_root_.GD.N0107.d009091 m n
                  (_root_.GD.N0107.d009085 ω.1)
                  (_root_.GD.N0107.d009085 ω.2),
                _root_.GD.N0107.d009093 m n ω))
        2 (_root_.GD.N0107.d009030 m n μ σ τ) := by
  have h :=
    _root_.GD.N0107.d012748
      m n hm hn μ σ τ hσ hτ q hq hB hqBound
  have hweight :
      (fun ω =>
        _root_.GD.N0107.d009038 m n μ σ τ
            (_root_.GD.N0107.d009046 m n σ τ)
            (_root_.GD.N0107.d009045 m n σ τ) ω *
          (_root_.GD.N0107.d009039 m n μ σ τ
              (_root_.GD.N0107.d009046 m n σ τ) ω -
            _root_.GD.N0107.d009046 m n σ τ)) =
      (fun ω =>
        _root_.GD.N0107.d009090 m n ω *
          (_root_.GD.N0107.d009091 m n
              (_root_.GD.N0107.d009085 ω.1)
              (_root_.GD.N0107.d009085 ω.2) -
            _root_.GD.N0107.d009046 m n σ τ)) := by
    funext ω
    rw [_root_.GD.N0107.d012724
      m n hm hn μ σ τ hσ hτ ω,
      _root_.GD.N0107.d012729
        m n hm hn μ σ τ hσ hτ ω]
  have hcarrier :
      (fun ω =>
        _root_.GD.N0107.d009038 m n μ σ τ
            (_root_.GD.N0107.d009046 m n σ τ)
            (_root_.GD.N0107.d009045 m n σ τ) ω *
          q
            (_root_.GD.N0107.d009039 m n μ σ τ
                (_root_.GD.N0107.d009046 m n σ τ) ω,
              _root_.GD.N0107.d009040 m n μ σ τ
                (_root_.GD.N0107.d009046 m n σ τ) ω)) =
      (fun ω =>
        _root_.GD.N0107.d009090 m n ω *
          q
            (_root_.GD.N0107.d009091 m n
                (_root_.GD.N0107.d009085 ω.1)
                (_root_.GD.N0107.d009085 ω.2),
              _root_.GD.N0107.d009093 m n ω)) := by
    funext ω
    rw [_root_.GD.N0107.d012724
      m n hm hn μ σ τ hσ hτ ω,
      _root_.GD.N0107.d012729
        m n hm hn μ σ τ hσ hτ ω,
      _root_.GD.N0107.d012731
        m n hm hn μ σ τ hσ hτ ω]
  rw [← hweight, ← hcarrier]
  exact h

end

end GD.N0107
