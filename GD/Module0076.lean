import GD.Module0075























open scoped BigOperators

namespace GD
namespace N0230
namespace N0606

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0683
open _root_.GD.N0230.N0630

variable {Θ Rule : Type*}




def d000961 (η : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |η n| < ε



def d000962
    (risk : Θ → Rule → ℝ)
    (J : ℕ → Rule → ℝ) (η : ℕ → ℝ)
    (bar d : Rule) : Prop :=
  _root_.GD.N0230.N0556.d000030 risk bar d ∧
    ∀ n e, _root_.GD.N0230.N0556.d000030 risk bar e → J n d ≤ J n e + η n



def d000963
    (risk : Θ → Rule → ℝ)
    (J : ℕ → Rule → ℝ) (d : Rule) : Prop :=
  ∀ e, _root_.GD.N0230.N0556.d000029 risk e d →
    ∃ ε, 0 < ε ∧ ∃ N, ∀ n, N ≤ n → J n e + ε ≤ J n d



theorem d000964
    {η : ℕ → ℝ}
    (hη : _root_.GD.N0230.N0606.d000961 η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → η n < ε := by
  obtain ⟨N, hN⟩ := hη ε hε
  refine ⟨N, ?_⟩
  intro n hn
  exact lt_of_le_of_lt (le_abs_self (η n)) (hN n hn)









theorem d000965
    (risk : Θ → Rule → ℝ)
    (J : ℕ → Rule → ℝ) (η : ℕ → ℝ)
    (bar d : Rule)
    (happrox : _root_.GD.N0230.N0606.d000962 risk J η bar d)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hdetect : _root_.GD.N0230.N0606.d000963 risk J d) :
    _root_.GD.N0230.N0556.d000031 risk d := by
  rintro ⟨e, he⟩
  have heBelow : _root_.GD.N0230.N0556.d000030 risk bar e :=
    _root_.GD.N0230.N0556.d000034 risk happrox.1 he.1
  obtain ⟨ε, hε, N, hgap⟩ := hdetect e he
  obtain ⟨M, herr⟩ := _root_.GD.N0230.N0606.d000964 hη hε
  let n := max N M
  have hnN : N ≤ n := le_max_left N M
  have hnM : M ≤ n := le_max_right N M
  have hmin := happrox.2 n e heBelow
  have hsep := hgap n hnN
  have hsmall := herr n hnM
  linarith



theorem d000966
    (risk : Θ → Rule → ℝ)
    (J : ℕ → Rule → ℝ) (η : ℕ → ℝ)
    (d : Rule)
    (happrox :
      ∀ n e, _root_.GD.N0230.N0556.d000028 risk e d → J n d ≤ J n e + η n)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hdetect : _root_.GD.N0230.N0606.d000963 risk J d) :
    _root_.GD.N0230.N0556.d000031 risk d := by
  apply _root_.GD.N0230.N0606.d000965
    risk J η d d
  · exact ⟨_root_.GD.N0230.N0556.d000032 risk d, happrox⟩
  · exact hη
  · exact hdetect



theorem d000967
    (risk : Θ → Rule → ℝ)
    (J : ℕ → Rule → ℝ) (η : ℕ → ℝ)
    (bar d : Rule)
    (happrox : _root_.GD.N0230.N0606.d000962 risk J η bar d)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hdetect : _root_.GD.N0230.N0606.d000963 risk J d) :
    _root_.GD.N0230.N0683.d000944 risk d := by
  exact
    (_root_.GD.N0230.N0683.d000946 risk d).mp
      (_root_.GD.N0230.N0606.d000965
        risk J η bar d happrox hη hdetect)



theorem d000968
    (risk : Θ → Rule → ℝ)
    (J : ℕ → Rule → ℝ) (η : ℕ → ℝ)
    (bar d : Rule)
    (happrox : _root_.GD.N0230.N0606.d000962 risk J η bar d)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hdetect : _root_.GD.N0230.N0606.d000963 risk J d)
    (hfaithful : _root_.GD.N0230.N0683.d000948 risk d) :
    _root_.GD.N0230.N0630.d000786 risk d := by
  apply _root_.GD.N0230.N0683.d000951
    risk
  · exact _root_.GD.N0230.N0606.d000967
      risk J η bar d happrox hη hdetect
  · exact hfaithful



section FiniteRiskSums


def d000969
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    (n : ℕ) (d : Rule) : ℝ :=
  ∑ θ ∈ F n, weight n θ * risk θ d


theorem d000970
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    (n : ℕ) (d e : Rule) :
    _root_.GD.N0230.N0606.d000969 risk F weight n d -
        _root_.GD.N0230.N0606.d000969 risk F weight n e =
      ∑ θ ∈ F n, weight n θ * (risk θ d - risk θ e) := by
  unfold _root_.GD.N0230.N0606.d000969
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro θ hθ
  ring

variable [DecidableEq Θ]









def d000971
    (risk : Θ → Rule → ℝ) (D : Set Θ) (d : Rule) : Prop :=
  ∀ e, _root_.GD.N0230.N0556.d000029 risk e d →
    ∃ θ, θ ∈ D ∧ risk θ e < risk θ d







theorem d000972
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    {e d : Rule}
    (hweak : _root_.GD.N0230.N0556.d000028 risk e d)
    {θ₀ : Θ} (hstrict : risk θ₀ e < risk θ₀ d)
    {a : ℝ} (ha : 0 < a)
    (hweight : ∀ n θ, θ ∈ F n → 0 ≤ weight n θ)
    (hseen : ∃ N, ∀ n, N ≤ n → θ₀ ∈ F n ∧ a ≤ weight n θ₀) :
    ∃ ε, 0 < ε ∧ ∃ N, ∀ n, N ≤ n →
      _root_.GD.N0230.N0606.d000969 risk F weight n e + ε ≤
        _root_.GD.N0230.N0606.d000969 risk F weight n d := by
  let Δ : ℝ := risk θ₀ d - risk θ₀ e
  have hΔ : 0 < Δ := sub_pos.mpr hstrict
  let ε : ℝ := a * Δ
  have hε : 0 < ε := mul_pos ha hΔ
  obtain ⟨N, hN⟩ := hseen
  refine ⟨ε, hε, N, ?_⟩
  intro n hn
  obtain ⟨hθ₀mem, haweight⟩ := hN n hn
  let f : Θ → ℝ := fun θ =>
    weight n θ * (risk θ d - risk θ e)
  have hf_nonneg : ∀ θ ∈ F n, 0 ≤ f θ := by
    intro θ hθ
    exact mul_nonneg
      (hweight n θ hθ)
      (sub_nonneg.mpr (hweak θ))
  have herase_nonneg :
      0 ≤ ∑ θ ∈ (F n).erase θ₀, f θ := by
    apply Finset.sum_nonneg
    intro θ hθ
    exact hf_nonneg θ (Finset.mem_of_mem_erase hθ)
  have hθ₀gap : ε ≤ f θ₀ := by
    exact mul_le_mul_of_nonneg_right haweight hΔ.le
  have hsum_split :
      ∑ θ ∈ F n, f θ =
        f θ₀ + ∑ θ ∈ (F n).erase θ₀, f θ := by
    calc
      (∑ θ ∈ F n, f θ) =
          (∑ θ ∈ (F n).erase θ₀, f θ) + f θ₀ :=
        (Finset.sum_erase_add (F n) f hθ₀mem).symm
      _ = f θ₀ + ∑ θ ∈ (F n).erase θ₀, f θ := by
        ac_rfl
  have hsum_gap : ε ≤ ∑ θ ∈ F n, f θ := by
    rw [hsum_split]
    linarith
  have hsub := _root_.GD.N0230.N0606.d000970 risk F weight n d e
  change
    _root_.GD.N0230.N0606.d000969 risk F weight n d -
        _root_.GD.N0230.N0606.d000969 risk F weight n e =
      ∑ θ ∈ F n, f θ at hsub
  linarith




theorem d000973
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    (d : Rule)
    (hweight : ∀ n θ, θ ∈ F n → 0 ≤ weight n θ)
    (hseen : ∀ θ, ∃ a, 0 < a ∧
      ∃ N, ∀ n, N ≤ n → θ ∈ F n ∧ a ≤ weight n θ) :
    _root_.GD.N0230.N0606.d000963
      risk (_root_.GD.N0230.N0606.d000969 risk F weight) d := by
  intro e he
  obtain ⟨θ₀, hstrict⟩ := he.2
  obtain ⟨a, ha, hθ₀seen⟩ := hseen θ₀
  exact _root_.GD.N0230.N0606.d000972
    risk F weight he.1 hstrict ha hweight hθ₀seen






theorem d000974
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    (D : Set Θ) (d : Rule)
    (hweight : ∀ n θ, θ ∈ F n → 0 ≤ weight n θ)
    (hwitness : _root_.GD.N0230.N0606.d000971 risk D d)
    (hseen : ∀ θ, θ ∈ D → ∃ a, 0 < a ∧
      ∃ N, ∀ n, N ≤ n → θ ∈ F n ∧ a ≤ weight n θ) :
    _root_.GD.N0230.N0606.d000963
      risk (_root_.GD.N0230.N0606.d000969 risk F weight) d := by
  intro e he
  obtain ⟨θ₀, hθ₀D, hstrict⟩ := hwitness e he
  obtain ⟨a, ha, hθ₀seen⟩ := hseen θ₀ hθ₀D
  exact _root_.GD.N0230.N0606.d000972
    risk F weight he.1 hstrict ha hweight hθ₀seen

section TopologicalWitnesses

variable [TopologicalSpace Θ]

omit [DecidableEq Θ] in





theorem d000975
    (risk : Θ → Rule → ℝ) (D : Set Θ) (d : Rule)
    (hD : Dense D)
    (hcontinuous : ∀ e, Continuous fun θ => risk θ d - risk θ e) :
    _root_.GD.N0230.N0606.d000971 risk D d := by
  intro e he
  obtain ⟨θ₀, hstrict⟩ := he.2
  let U : Set Θ := {θ | 0 < risk θ d - risk θ e}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const (hcontinuous e)
  have hUne : U.Nonempty := by
    exact ⟨θ₀, sub_pos.mpr hstrict⟩
  obtain ⟨θ, hθD, hθU⟩ := hD.exists_mem_open hUopen hUne
  exact ⟨θ, hθD, sub_pos.mp hθU⟩

end TopologicalWitnesses


theorem d000976
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    (η : ℕ → ℝ) (bar d : Rule)
    (happrox : _root_.GD.N0230.N0606.d000962
      risk (_root_.GD.N0230.N0606.d000969 risk F weight) η bar d)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hweight : ∀ n θ, θ ∈ F n → 0 ≤ weight n θ)
    (hseen : ∀ θ, ∃ a, 0 < a ∧
      ∃ N, ∀ n, N ≤ n → θ ∈ F n ∧ a ≤ weight n θ) :
    _root_.GD.N0230.N0556.d000031 risk d := by
  apply _root_.GD.N0230.N0606.d000965
    risk (_root_.GD.N0230.N0606.d000969 risk F weight) η bar d happrox hη
  exact _root_.GD.N0230.N0606.d000973
    risk F weight d hweight hseen





theorem d000977
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    (D : Set Θ)
    (η : ℕ → ℝ) (bar d : Rule)
    (happrox : _root_.GD.N0230.N0606.d000962
      risk (_root_.GD.N0230.N0606.d000969 risk F weight) η bar d)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hweight : ∀ n θ, θ ∈ F n → 0 ≤ weight n θ)
    (hwitness : _root_.GD.N0230.N0606.d000971 risk D d)
    (hseen : ∀ θ, θ ∈ D → ∃ a, 0 < a ∧
      ∃ N, ∀ n, N ≤ n → θ ∈ F n ∧ a ≤ weight n θ) :
    _root_.GD.N0230.N0556.d000031 risk d := by
  apply _root_.GD.N0230.N0606.d000965
    risk (_root_.GD.N0230.N0606.d000969 risk F weight) η bar d happrox hη
  exact _root_.GD.N0230.N0606.d000974
    risk F weight D d hweight hwitness hseen


theorem d000978
    (risk : Θ → Rule → ℝ)
    (F : ℕ → Finset Θ) (weight : ℕ → Θ → ℝ)
    (η : ℕ → ℝ) (bar d : Rule)
    (happrox : _root_.GD.N0230.N0606.d000962
      risk (_root_.GD.N0230.N0606.d000969 risk F weight) η bar d)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hweight : ∀ n θ, θ ∈ F n → 0 ≤ weight n θ)
    (hseen : ∀ θ, ∃ a, 0 < a ∧
      ∃ N, ∀ n, N ≤ n → θ ∈ F n ∧ a ≤ weight n θ) :
    _root_.GD.N0230.N0683.d000944 risk d := by
  exact
    (_root_.GD.N0230.N0683.d000946 risk d).mp
      (_root_.GD.N0230.N0606.d000976
        risk F weight η bar d happrox hη hweight hseen)

end FiniteRiskSums



section DenseSampledRiskSums




def d000979
    (risk : Θ → Rule → ℝ)
    (sample : ℕ → Θ) (weight : ℕ → ℝ)
    (n : ℕ) (d : Rule) : ℝ :=
  ∑ i ∈ Finset.range n, weight i * risk (sample i) d



theorem d000980
    (risk : Θ → Rule → ℝ)
    (sample : ℕ → Θ) (weight : ℕ → ℝ)
    {e d : Rule}
    (hweak : _root_.GD.N0230.N0556.d000028 risk e d)
    {i₀ : ℕ} (hstrict : risk (sample i₀) e < risk (sample i₀) d)
    (hweight : 0 < weight i₀)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) :
    ∃ ε, 0 < ε ∧ ∃ N, ∀ n, N ≤ n →
      _root_.GD.N0230.N0606.d000979 risk sample weight n e + ε ≤
        _root_.GD.N0230.N0606.d000979 risk sample weight n d := by
  let sampledRisk : ℕ → Rule → ℝ := fun i a ↦ risk (sample i) a
  have hweakSample : _root_.GD.N0230.N0556.d000028 sampledRisk e d := fun i ↦ hweak (sample i)
  have hseen :
      ∃ N, ∀ n, N ≤ n →
        i₀ ∈ Finset.range n ∧ weight i₀ ≤ weight i₀ := by
    refine ⟨i₀ + 1, ?_⟩
    intro n hn
    exact
      ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self i₀) hn),
        le_rfl⟩
  simpa [_root_.GD.N0230.N0606.d000979, _root_.GD.N0230.N0606.d000969, sampledRisk] using
    (_root_.GD.N0230.N0606.d000972
      sampledRisk (fun n ↦ Finset.range n) (fun _ i ↦ weight i)
      hweakSample hstrict hweight
      (fun _ i _ ↦ hweight_nonneg i) hseen)





theorem d000981
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ)
    (sample : ℕ → Θ) (weight : ℕ → ℝ)
    (hdense : DenseRange sample)
    (hweight : ∀ i, 0 < weight i)
    (hcontinuous : ∀ e,
      _root_.GD.N0230.N0556.d000028 risk e d →
        Continuous (fun θ ↦ risk θ d - risk θ e)) :
    _root_.GD.N0230.N0606.d000963
      risk (_root_.GD.N0230.N0606.d000979 risk sample weight) d := by
  intro e he
  obtain ⟨θ₀, hstrict₀⟩ := he.2
  let U : Set Θ := {θ | 0 < risk θ d - risk θ e}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const (hcontinuous e he.1)
  have hUne : U.Nonempty := by
    exact ⟨θ₀, sub_pos.mpr hstrict₀⟩
  obtain ⟨i₀, hi₀⟩ := hdense.exists_mem_open hUopen hUne
  have hstrictSample : risk (sample i₀) e < risk (sample i₀) d :=
    sub_pos.mp hi₀
  exact _root_.GD.N0230.N0606.d000980
    risk sample weight he.1 hstrictSample (hweight i₀)
      (fun i ↦ (hweight i).le)




theorem d000982
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ)
    (sample : ℕ → Θ) (weight : ℕ → ℝ)
    (η : ℕ → ℝ) (bar d : Rule)
    (happrox : _root_.GD.N0230.N0606.d000962
      risk (_root_.GD.N0230.N0606.d000979 risk sample weight) η bar d)
    (hη : _root_.GD.N0230.N0606.d000961 η)
    (hdense : DenseRange sample)
    (hweight : ∀ i, 0 < weight i)
    (hcontinuous : ∀ e,
      _root_.GD.N0230.N0556.d000028 risk e d →
        Continuous (fun θ ↦ risk θ d - risk θ e)) :
    _root_.GD.N0230.N0556.d000031 risk d := by
  apply _root_.GD.N0230.N0606.d000965
    risk (_root_.GD.N0230.N0606.d000979 risk sample weight) η bar d happrox hη
  exact _root_.GD.N0230.N0606.d000981
    risk sample weight hdense hweight hcontinuous

end DenseSampledRiskSums

end N0606
end N0230
end GD
