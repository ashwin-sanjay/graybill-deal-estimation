import GD.Module0615
















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137



def d009018 (n : ℕ) (μ σ : ℝ) :
    _root_.GD.N0137.d008894 n → _root_.GD.N0137.d008894 n :=
  fun z i => μ + σ * z i


def d009019 (n : ℕ) (μ σ : ℝ) :
    _root_.GD.N0137.d008894 n → _root_.GD.N0137.d008894 n :=
  fun x i => (x i - μ) / σ

@[fun_prop] theorem d009020
    (n : ℕ) (μ σ : ℝ) :
    Measurable (_root_.GD.N0107.d009018 n μ σ) := by
  unfold _root_.GD.N0107.d009018
  fun_prop

@[fun_prop] theorem d009021
    (n : ℕ) (μ σ : ℝ) :
    Measurable (_root_.GD.N0107.d009019 n μ σ) := by
  unfold _root_.GD.N0107.d009019
  fun_prop

theorem d009022
    (n : ℕ) (μ σ : ℝ) (hσ : σ ≠ 0)
    (z : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009019 n μ σ (_root_.GD.N0107.d009018 n μ σ z) = z := by
  funext i
  unfold _root_.GD.N0107.d009019 _root_.GD.N0107.d009018
  field_simp
  ring

theorem d009023
    (n : ℕ) (μ σ : ℝ) (hσ : σ ≠ 0)
    (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009018 n μ σ (_root_.GD.N0107.d009019 n μ σ x) = x := by
  funext i
  unfold _root_.GD.N0107.d009019 _root_.GD.N0107.d009018
  field_simp
  ring



def d009024 (m n : ℕ) (μ σ τ : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) →
      (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :=
  fun ω => (_root_.GD.N0107.d009018 m μ σ ω.1, _root_.GD.N0107.d009018 n μ τ ω.2)


def d009025 (m n : ℕ) (μ σ τ : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) →
      (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :=
  fun ω =>
    (_root_.GD.N0107.d009019 m μ σ ω.1, _root_.GD.N0107.d009019 n μ τ ω.2)

@[fun_prop] theorem d009026
    (m n : ℕ) (μ σ τ : ℝ) :
    Measurable (_root_.GD.N0107.d009024 m n μ σ τ) := by
  unfold _root_.GD.N0107.d009024
  fun_prop

@[fun_prop] theorem d009027
    (m n : ℕ) (μ σ τ : ℝ) :
    Measurable (_root_.GD.N0107.d009025 m n μ σ τ) := by
  unfold _root_.GD.N0107.d009025
  fun_prop

theorem d009028
    (m n : ℕ) (μ σ τ : ℝ)
    (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009025 m n μ σ τ
        (_root_.GD.N0107.d009024 m n μ σ τ ω) = ω := by
  ext
  · exact congrFun (_root_.GD.N0107.d009022 m μ σ hσ ω.1) _
  · exact congrFun (_root_.GD.N0107.d009022 n μ τ hτ ω.2) _

theorem d009029
    (m n : ℕ) (μ σ τ : ℝ)
    (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009024 m n μ σ τ
        (_root_.GD.N0107.d009025 m n μ σ τ ω) = ω := by
  ext
  · exact congrFun (_root_.GD.N0107.d009023 m μ σ hσ ω.1) _
  · exact congrFun (_root_.GD.N0107.d009023 n μ τ hτ ω.2) _




def d009030 (m n : ℕ) (μ σ τ : ℝ) :
    Measure (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :=
  (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0107.d009024 m n μ σ τ)

noncomputable instance (m n : ℕ) (μ σ τ : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0107.d009030 m n μ σ τ) := by
  unfold _root_.GD.N0107.d009030
  exact Measure.isProbabilityMeasure_map
    (_root_.GD.N0107.d009026 m n μ σ τ).aemeasurable



theorem d009031
    (m n : ℕ) (μ σ τ : ℝ)
    (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    (_root_.GD.N0107.d009030 m n μ σ τ).map
        (_root_.GD.N0107.d009025 m n μ σ τ) =
      _root_.GD.N0137.d008914 m n := by
  unfold _root_.GD.N0107.d009030
  rw [Measure.map_map]
  · have hfun :
        _root_.GD.N0107.d009025 m n μ σ τ ∘
            _root_.GD.N0107.d009024 m n μ σ τ = id := by
      funext ω
      exact _root_.GD.N0107.d009028
        m n μ σ τ hσ hτ ω
    rw [hfun, Measure.map_id]
  · exact _root_.GD.N0107.d009027 m n μ σ τ
  · exact _root_.GD.N0107.d009026 m n μ σ τ



def d009032
    (m n : ℕ) (μ σ τ e : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0137.d008932 m n e ∘
    _root_.GD.N0107.d009025 m n μ σ τ

def d009033 (m n : ℕ) (μ σ τ : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0137.d008933 m n ∘ _root_.GD.N0107.d009025 m n μ σ τ

def d009034 (m n : ℕ) (μ σ τ : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0137.d008934 m n ∘ _root_.GD.N0107.d009025 m n μ σ τ

def d009035
    (m n : ℕ) (μ σ τ e : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) →
      _root_.GD.N0124.d006387 :=
  _root_.GD.N0137.d008935 m n e ∘ _root_.GD.N0107.d009025 m n μ σ τ

@[fun_prop] theorem d009036
    (m n : ℕ) (μ σ τ e : ℝ) :
    Measurable (_root_.GD.N0107.d009035 m n μ σ τ e) := by
  unfold _root_.GD.N0107.d009035
  fun_prop



theorem d009037
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    _root_.GD.N0125.d008841
      (_root_.GD.N0107.d009030 m n μ σ τ)
      (_root_.GD.N0107.d009032 m n μ σ τ e)
      (_root_.GD.N0107.d009033 m n μ σ τ)
      (_root_.GD.N0107.d009034 m n μ σ τ)
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2) := by
  change
    (_root_.GD.N0107.d009030 m n μ σ τ).map
        (_root_.GD.N0107.d009035 m n μ σ τ e) =
      _root_.GD.N0125.d008840
        (((m - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)
  calc
    (_root_.GD.N0107.d009030 m n μ σ τ).map
        (_root_.GD.N0107.d009035 m n μ σ τ e) =
      ((_root_.GD.N0107.d009030 m n μ σ τ).map
        (_root_.GD.N0107.d009025 m n μ σ τ)).map
          (_root_.GD.N0137.d008935 m n e) := by
        rw [Measure.map_map]
        · rfl
        · exact _root_.GD.N0137.d008937 m n e
        · exact _root_.GD.N0107.d009027 m n μ σ τ
    _ = (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008935 m n e) := by
      rw [_root_.GD.N0107.d009031
        m n μ σ τ hσ hτ]
    _ = _root_.GD.N0125.d008840
          (((m - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2) := by
      exact _root_.GD.N0137.d008938
        m n hm hn he0 he1


def d009038
    (m n : ℕ) (μ σ τ e Sigma : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0137.d008942 m n e Sigma ∘ _root_.GD.N0107.d009025 m n μ σ τ

def d009039
    (m n : ℕ) (μ σ τ e : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0137.d008943 m n e ∘ _root_.GD.N0107.d009025 m n μ σ τ

def d009040
    (m n : ℕ) (μ σ τ e : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0137.d008944 m n e ∘ _root_.GD.N0107.d009025 m n μ σ τ

@[fun_prop] theorem d009041
    (m n : ℕ) (μ σ τ e Sigma : ℝ) :
    Measurable (fun ω =>
      (_root_.GD.N0107.d009038 m n μ σ τ e Sigma ω,
        (_root_.GD.N0107.d009039 m n μ σ τ e ω,
          _root_.GD.N0107.d009040 m n μ σ τ e ω))) := by
  unfold _root_.GD.N0107.d009038 _root_.GD.N0107.d009039 _root_.GD.N0107.d009040
  exact (_root_.GD.N0137.d008946 m n e Sigma).comp
    (_root_.GD.N0107.d009027 m n μ σ τ)



theorem d009042
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    {e Sigma : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hSigma : 0 ≤ Sigma) :
    _root_.GD.N0125.d008847
      (_root_.GD.N0107.d009030 m n μ σ τ)
      (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
      (_root_.GD.N0107.d009039 m n μ σ τ e)
      (_root_.GD.N0107.d009040 m n μ σ τ e)
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2)
      e Sigma := by
  apply _root_.GD.N0125.d008876
  · exact _root_.GD.N0137.d008900 hm
  · exact _root_.GD.N0137.d008900 hn
  · exact hSigma
  · exact _root_.GD.N0107.d009036 m n μ σ τ e
  · exact _root_.GD.N0107.d009037
      m n hm hn μ σ τ hσ hτ he0 he1
  · intro ω
    rfl
  · intro ω
    rfl
  · intro ω
    rfl


def d009043 (m : ℕ) (σ : ℝ) : ℝ :=
  σ ^ 2 / m


def d009044 (n : ℕ) (τ : ℝ) : ℝ :=
  τ ^ 2 / n


def d009045 (m n : ℕ) (σ τ : ℝ) : ℝ :=
  _root_.GD.N0107.d009043 m σ + _root_.GD.N0107.d009044 n τ



def d009046 (m n : ℕ) (σ τ : ℝ) : ℝ :=
  _root_.GD.N0107.d009044 n τ / _root_.GD.N0107.d009045 m n σ τ

theorem d009047
    {m : ℕ} (hm : 0 < m) {σ : ℝ} (hσ : 0 < σ) :
    0 < _root_.GD.N0107.d009043 m σ := by
  unfold _root_.GD.N0107.d009043
  positivity

theorem d009048
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) :
    0 < _root_.GD.N0107.d009044 n τ := by
  unfold _root_.GD.N0107.d009044
  positivity

theorem d009049
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < _root_.GD.N0107.d009045 m n σ τ := by
  unfold _root_.GD.N0107.d009045
  exact add_pos
    (_root_.GD.N0107.d009047 hm hσ)
    (_root_.GD.N0107.d009048 hn hτ)

theorem d009050
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < _root_.GD.N0107.d009046 m n σ τ := by
  unfold _root_.GD.N0107.d009046
  exact div_pos (_root_.GD.N0107.d009048 hn hτ)
    (_root_.GD.N0107.d009049 hm hn hσ hτ)

theorem d009051
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    _root_.GD.N0107.d009046 m n σ τ < 1 := by
  unfold _root_.GD.N0107.d009046 _root_.GD.N0107.d009045
  have hx := _root_.GD.N0107.d009047 hm hσ
  have hy := _root_.GD.N0107.d009048 hn hτ
  rw [div_lt_one (add_pos hx hy)]
  linarith




theorem d009052
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    _root_.GD.N0125.d008847
      (_root_.GD.N0107.d009030 m n μ σ τ)
      (_root_.GD.N0107.d009038 m n μ σ τ
        (_root_.GD.N0107.d009046 m n σ τ)
        (_root_.GD.N0107.d009045 m n σ τ))
      (_root_.GD.N0107.d009039 m n μ σ τ
        (_root_.GD.N0107.d009046 m n σ τ))
      (_root_.GD.N0107.d009040 m n μ σ τ
        (_root_.GD.N0107.d009046 m n σ τ))
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2)
      (_root_.GD.N0107.d009046 m n σ τ)
      (_root_.GD.N0107.d009045 m n σ τ) := by
  apply _root_.GD.N0107.d009042
    m n hm hn μ σ τ hσ.ne' hτ.ne'
  · exact (_root_.GD.N0107.d009050 (by omega) (by omega) hσ hτ).le
  · exact (_root_.GD.N0107.d009051
      (by omega) (by omega) hσ hτ).le
  · exact (_root_.GD.N0107.d009049
      (by omega) (by omega) hσ hτ).le

end

end GD.N0107
