module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ExteriorPrimeTrace
import RiemannMasullo.ForMathlib.Analysis.Fourier.SparseLaplaceProbe
import Mathlib.Tactic

/-! # A fixed-window criterion for the signed exterior comparison

Even with both poles killed and a finite list of critical Mellin values prescribed,
one may test each missing right-hand order in any positive log window. -/

@[expose] public noncomputable section

open Classical Function MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.RationalWidthLoss
set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Z" => {ρ : ℂ // 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ}
local notation "w(" ρ ")" => ((ρ : Z).val - (1/2 : ℂ))
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (logIdeleClassNorm ℚ x)
local notation "freq(" t ")" => (((t : ℝ) : ℂ)*Complex.I)
local notation "B(" H ", " z ")" => bilateralLaplace H z

/-- The physical prime comparison for all normalized polar-free probes in one
fixed log window with a prescribed finite list of critical Mellin samples. -/
def UniversalExteriorPrimeMatch {ι : Type*} [Fintype ι] (γ : ι → ℝ) (v : ι → ℂ)
    {a : ℝ} (ha : 0 ≤ a) (c ε : ℝ) : Prop :=
  ∀ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ), ContDiff ℝ (∞) H →
    tsupport H ⊆ Icc (c-ε) (c+ε) → H c = 1 → radial(φ,H) →
    B(H,1/2) = 0 → B(H,-(1/2)) = 0 → (∀ j, B(H,freq(γ j)) = v j) →
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      (exteriorStripTrace ha φ y + V*rationalFirstPrimeSum (fun x ↦ H (x-y)))) (Ioi 0)

private theorem zero_re_lt_one (ρ : Z) : ρ.val.re < 1 := by
  apply (re_mem_Ioo ⟨ρ.val,?_⟩).2
  change 0 < MeromorphicOn.divisor _ _ _
  rw [principal_divisor_eq_completedRiemannZeta]
  exact ρ.property

private theorem exists_detecting_probe {ι : Type*} [Fintype ι] (γ : ι → ℝ) (hγ : Injective γ)
    (v : ι → ℂ) (ρ : Z) (hρ : 1/2 < ρ.val.re) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c-ε) (c+ε) ∧ H c = 1 ∧
      B(H,1/2) = 0 ∧ B(H,-(1/2)) = 0 ∧ (∀ j, B(H,freq(γ j)) = v j) ∧ B(H,w(ρ)) = 1 := by
  let r : Option ι → ℂ := fun j ↦ j.elim w(ρ) (fun k ↦ freq(γ k))
  let p : Bool → ℂ := fun b ↦ if b then 1/2 else -(1/2)
  have hre : w(ρ).re = ρ.val.re-1/2 := by norm_num
  have hpos : 0 < w(ρ).re := by linarith
  have hlt : w(ρ).re < 1/2 := by linarith [zero_re_lt_one ρ]
  have sep (j : ι) : w(ρ) ≠ freq(γ j) := by
    intro he
    have h := congrArg Complex.re he
    norm_num at h
    linarith
  have hr : Injective r := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (sep j he).elim
    | some i =>
      cases j with
      | none => exact (sep i he.symm).elim
      | some j =>
        have h : γ i = γ j := by simpa [r] using congrArg Complex.im he
        exact congrArg some (hγ h)
  have hw (b : Bool) (j : Option ι) : p b ≠ r j := by
    intro he
    have h := congrArg Complex.re he
    cases b <;> cases j <;> norm_num [p,r] at h <;> linarith
  have hw₀ (b : Bool) : p b ≠ (2 : ℝ) := by cases b <;> norm_num [p]
  have hr₀ (j : Option ι) : r j ≠ (2 : ℝ) := by
    intro he
    have h := congrArg Complex.re he
    cases j <;> norm_num [r] at h; linarith
  obtain ⟨H,hH,hb,hc,hp,hrv⟩ := SparseLaplace.exists_complex_interpolating_probe p
    (hasSum_fintype _).summable r hr hw 2 hw₀ hr₀ (fun j : Option ι ↦ j.elim 1 v) c hε
  exact ⟨H,hH,hb,hc,by simpa [p] using hp true,by simpa [p] using hp false,
    fun j ↦ hrv (some j),hrv none⟩

/-- Universal matching at one width, in any one positive log window, is equivalent
to full retention of the order of every right-hand zeta zero. The statement
includes the partially retained boundary orders. -/
theorem universalExteriorPrimeMatch_iff {ι : Type*} [Fintype ι] (γ : ι → ℝ) (hγ : Injective γ) (v : ι → ℂ)
    {a c ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hl : ε < c) :
    UniversalExteriorPrimeMatch γ v ha.le c ε ↔ ∀ ρ : Z, 1/2 < ρ.val.re → omittedOrder a ρ = 0 := by
  constructor
  · intro hall ρ hρ
    by_contra! hm
    obtain ⟨H,hH,hb,hc,hp,hm',hv,hone⟩ := exists_detecting_probe γ hγ v ρ hρ c hε
    obtain ⟨φ,hφ⟩ := exists_normTest (F := ℚ) H hH (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb)
    have h := (exterior_firstPrime_iff_right_samples ha (sub_pos.mpr hl) H hH hb hp φ hφ).mp
      (hall H φ hH hb hc hφ hp hm' hv) ρ hρ (Nat.pos_of_ne_zero hm)
    exact one_ne_zero (hone.symm.trans h)
  · intro hall H φ hH hb _ hφ hp _ _
    apply (exterior_firstPrime_iff_right_samples ha (sub_pos.mpr hl) H hH hb hp φ hφ).mpr
    intro ρ hρ hpos
    exact (hpos.ne' (hall ρ hρ)).elim

end RiemannMasullo.RationalWidthLoss
