module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.QuotientLayer
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearRetraction
public import Mathlib.LinearAlgebra.Trace

/-! # Nuclear trace-norm lower bounds from finite quotients -/

public noncomputable section
open Set Function Module
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a finite-dimensional Hilbert space the nuclear trace is the algebraic
trace in any basis, with no orthogonality assumption on that basis. -/
theorem nuclear_trace_finiteBasis {ι : Type*} [Fintype ι] (b : Basis ι ℂ H) (A : H →L[ℂ] H) :
    ∃ hA : IsNuclearOperator A,
      hilbertTrace ⟨A,hA⟩ = ∑ i, b.repr (A (b i)) i := by
  classical
  let : FiniteDimensional ℂ H := b.finiteDimensional_of_finite
  let φ (i : ι) : H →L[ℂ] ℂ := (b.coord i).toContinuousLinearMap
  let R (i : ι) : H →L[ℂ] H := (φ i).smulRight (A (b i))
  have hR (i : ι) : IsNuclearOperator (R i) := isNuclearOperator_smulRight _ _
  have he : ∑ i, R i = A := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sum_apply, R, ContinuousLinearMap.smulRight_apply]
    have hh := congrArg A (b.sum_repr x)
    simpa only [map_sum, map_smul] using! hh
  have hn : IsNuclearOperator (∑ i, R i) := (nuclearEndomorphisms H).sum_mem (fun i _ ↦ hR i)
  have hA : IsNuclearOperator A := he ▸ hn
  obtain ⟨tr,htr⟩ := hilbertTrace_linear (H := H)
  have hs : (⟨A,hA⟩ : nuclearEndomorphisms H) = ∑ i, ⟨R i,hR i⟩ := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using! he.symm
  refine ⟨hA, ?_⟩
  rw [← htr, hs, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [htr]
  exact hilbertTrace_smulRight (φ i) (A (b i))


/-- A finite quotient with a constant diagonal forces the corresponding linear
lower bound on the trace norm of the upstairs nuclear operator. The quotient
coordinates may be nonorthogonal; their norm does not enter the bound. -/
theorem traceNorm_ge_finite_quotient_diagonal (m : ℕ)
    (L : H →L[ℂ] (Fin m → ℂ)) (hL : Surjective L)
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A)
    (B : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hAB : ∀ x, L (A x) = B (L x)) (c : ℂ)
    (hdiag : ∀ i : Fin m, B (Pi.single i 1) i = c) :
    (m : ℝ) * ‖c‖ ≤ traceNorm ⟨A,hA⟩ := by
  classical
  let K : ClosedSubmodule ℂ H := ⟨L.ker, L.isClosed_ker⟩
  let : IsClosed (K.toSubmodule : Set H) := K.isClosed
  let Q := H ⧸ K.toSubmodule
  let q : H →L[ℂ] Q := K.toSubmodule.mkQL
  let J : Q →ₗᵢ[ℂ] H := quotientOrthogonalSection K
  let e : Q ≃ₗ[ℂ] (Fin m → ℂ) := L.toLinearMap.quotKerEquivOfSurjective hL
  let b : Basis (Fin m) ℂ Q := Basis.ofEquivFun e
  let AQ : Q →L[ℂ] Q := q.comp (A.comp J.toContinuousLinearMap)
  have heq (x : H) : e (q x) = L x :=
    LinearMap.quotKerEquivOfSurjective_apply_mk L.toLinearMap hL x
  have hqJ (x : Q) : q (J x) = x := quotientOrthogonalSection_rightInverse K x
  have hEA (x : Q) : e (AQ x) = B (e x) := by
    change e (q (A (J x))) = B (e x)
    rw [heq, hAB, ← heq, hqJ]
  obtain ⟨hn,htrace⟩ := nuclear_trace_finiteBasis b AQ
  have htrace' : hilbertTrace ⟨AQ,hn⟩ = (m : ℂ) * c := by
    rw [htrace]
    have hd (i : Fin m) : b.repr (AQ (b i)) i = c := by
      rw [show b = Basis.ofEquivFun e from rfl, Basis.ofEquivFun_repr_apply, hEA]
      simp only [Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
      exact hdiag i
    simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hqnorm : ‖q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    exact (Submodule.Quotient.norm_mk_le K.toSubmodule x).trans_eq (one_mul _).symm
  have hprod : ‖q‖ * ‖J.toContinuousLinearMap‖ ≤ 1 :=
    (mul_le_mul hqnorm J.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  obtain ⟨hn',hb⟩ := traceNorm_sandwich_le A hA J.toContinuousLinearMap q
  have hb' : traceNorm ⟨AQ,hn⟩ ≤ traceNorm ⟨A,hA⟩ := by
    apply hb.trans
    exact (mul_le_mul_of_nonneg_right hprod
      ((norm_nonneg (hilbertTrace ⟨A,hA⟩)).trans (norm_hilbertTrace_le _))).trans_eq (one_mul _)
  have ht := (norm_hilbertTrace_le (⟨AQ,hn⟩ : nuclearEndomorphisms Q)).trans hb'
  rw [htrace', norm_mul, Complex.norm_natCast] at ht
  exact ht

end RiemannMasullo
