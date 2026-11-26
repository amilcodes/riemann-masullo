module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CylinderMeanSquare
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CylinderStripTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec5_SignedHeightCutoff
import Mathlib.Tactic

/-! # The signed sharp local limit on rational residue cylinders

The full-width operator measures a finite-conductor prime and archimedean
sum with its two polar moments. At a smaller width the difference is a
finite Fourier average of primitive zero jets, with their complex signs.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory Set NumberField
open scoped ComplexConjugate ContDiff NumberField.AdeleRing Topology

namespace RiemannMasullo.ConductorCylinder

open ConductorDensity RationalConductor NumberFieldKB.Chebotarev.RatIdele

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSpectralQuotientPolynormableSec3 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Zstrip" => {z : ℂ // 0 < z.re ∧ z.re < 1}
local notation "full(" q ", " φ ")" => physicalWidthSum q φ (1/2) (fun _ _ m ↦ (m : ℂ))
local notation "trace(" ha ", " hs ", " φ ")" => halfTwistStripTrace (F := ℚ) ha hs φ
local notation "ord(" i ")" => completedPrimitiveOrder i
local notation "miss(" a ", " s ", " i ")" => (ord(i) -
  spectralStripMultiplicity a s ((i).2.val.re - 1/2) (ord(i)) : ℕ)
local notation "G(" H ")" => shiftedProfile (1/2) H
local notation "poles(" q ", " H ")" =>
  (bilateralLaplace H (-(1/2)) + bilateralLaplace H (1/2)) / ((q : ℕ).totient : ℂ)
local notation "mass(" φ ", " f ", " R ")" => -correctedSLocalTraceSharpMass φ f R
local notation "LiftAt(" φ ", " S ", " f ")" => ∀ g : (SAdeleRing ℚ S)ˣ,
  HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ).val (ξ.val*g))
    ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))

private theorem trace_eq_retained (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 1 < s) : trace(ha,hs,φ) = physicalCenteredRetained q φ a s :=
  (halfTwistStripTrace_eq_hilbertTrace ha hs φ ⟨_, spectralStripConvolution_nuclear_of_summable_clusterTraceNorms
    (1/2) ha (zero_lt_one.trans hs).le φ⟩ rfl).trans
    (hilbertTrace_eq_physicalCenteredRetained q r H φ hφ ha hs _ rfl)

private theorem retained_eq_full (q : ℕ) [NeZero q] (φ : BruhatCompactSupport Cℚ)
    {a : ℝ} (ha : 1/2 ≤ a) (s : ℝ) : physicalCenteredRetained q φ a s = full(q,φ) := by
  unfold physicalCenteredRetained physicalWidthSum
  apply Finset.sum_congr rfl
  intro χ _
  apply tsum_congr fun z ↦ ?_
  have hz := rowZeroSites_mem_criticalStrip (packetRow χ) z
  dsimp only
  rw [spectralStripMultiplicity_interior (show z.val.re - 1/2 ∈ Ioo (-a) a from
    ⟨by linarith [hz.1], by linarith [hz.2]⟩)]

private theorem wide_eq_full (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ) :
    trace((by norm_num : (0:ℝ) ≤ 1/2), (by norm_num : (1:ℝ) < 3), φ) = full(q,φ) :=
  (trace_eq_retained q r H φ hφ _ _).trans (retained_eq_full q φ le_rfl 3)

/-- Paper: §12.3 and §12.5.1.1, pp. 514, 520. A single finite-place lift
computes the signed local limit and its difference from every centered
Hilbert trace. The full limit retains the two polar moments; the signed
difference measures exactly the missing primitive jets. -/
theorem exists_sharpMass_cylinder_signed_comparison (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ) (S₀ : Finset Vℚ) :
    ∃ (S : Finset Vℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ), S₀ ⊆ S ∧ LiftAt(φ,S,f) ∧
      Tendsto (fun R : ℝ ↦ mass(φ,f,R)) atTop (𝓝 (poles(q,H) +
        cylinderAverage q r (primeAndArchRow G(H) (archTerm 0 G(H)) (archTerm 1 G(H))))) ∧
      ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
        Tendsto (fun R : ℝ ↦ mass(φ,f,R) - trace(ha,hs,φ)) atTop
          (𝓝 (cylinderAverage q r (fun χ ↦ ∑' z : Zstrip,
            (miss(a,s,(χ,z)) : ℂ) * bilateralLaplace H (z.val-1/2)))) := by
  obtain ⟨S,f,hS,hf,hlim⟩ := exists_correctedSharpMass_tendsto_fullTrace φ S₀
  rw [wide_eq_full q r H φ hφ] at hlim
  refine ⟨S,f,hS,hf,?_,?_⟩
  · have he := physicalFull_eq_poles_add_primeAndArchRow q r (1/2) H hd hc hp φ hφ
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      show (1:ℂ)-1/2=1/2 by norm_num] at he
    rwa [← he]
  · intro a s ha hs
    rw [trace_eq_retained q r H φ hφ ha hs, ← physicalFull_sub_retained q r a s H hd hc hp φ hφ]
    exact hlim.sub_const _

/-- Paper: §12.5.1.1, p. 520. With a fixed profile, every sufficiently large
prime modulus isolates exactly one von Mangoldt coefficient. Both the local
limit and every full-width Hilbert trace give that signed value. -/
theorem exists_sharpMass_prime_cylinder {b : ℕ} (hb : 2 ≤ b)
    (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (S₀ : Finset Vℚ) :
    ∃ L : ℕ, ∀ {q : ℕ} [NeZero q], q.Prime → L ≤ q → ∀ (hbq : b.Coprime q),
      ∃ (φ : BruhatCompactSupport Cℚ) (S : Finset Vℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
        IsNormalizedCylinder q (ZMod.unitOfCoprime b hbq) H φ ∧ S₀ ⊆ S ∧ LiftAt(φ,S,f) ∧
        let P := poles(q,H) - (((b : ℝ)^(-(1/2):ℝ) : ℝ) : ℂ) * primeSample H b
        Tendsto (fun R : ℝ ↦ mass(φ,f,R)) atTop (𝓝 P) ∧
        ∀ {a s : ℝ} (ha : 1/2 ≤ a) (hs : 1 < s), trace((show 0 ≤ a by linarith),hs,φ) = P := by
  obtain ⟨L,hL⟩ := physicalFull_eq_prime_sample hb (1/2) H hd hc hp
  refine ⟨L,?_⟩
  intro q _ hq hqL hbq
  let r := ZMod.unitOfCoprime b hbq
  let φ := selectedCylinder q r H hd hc
  have hφ := selectedCylinder_spec q r H hd hc
  obtain ⟨S,f,hS,hf,hlim⟩ := exists_correctedSharpMass_tendsto_fullTrace φ S₀
  have he := hL hq hqL hbq φ hφ
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    show (1:ℂ)-1/2=1/2 by norm_num] at he
  rw [wide_eq_full q r H φ hφ, he] at hlim
  refine ⟨φ,S,f,hφ,hS,hf,hlim,?_⟩
  intro a s ha hs
  rw [trace_eq_retained q r H φ hφ, retained_eq_full q φ ha, he]

/-- For the principal character both polar Mellin values on the physical
cylinder have exactly the cylinder-volume normalization, separately. -/
theorem principal_cylinder_mellin (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : Continuous H) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ)
    (z : ℂ) :
    modulatedFourierMellin (continuousIdeleClassNorm ℚ) univ
      ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ (ideleClassTamagawaMeasure ℚ)
      φ.val (ideleClassNormTwist 1 z) = bilateralLaplace H z / q.totient := by
  rw [normalized_cylinder_mellin q r H hH φ hφ 1 1 (fun x ↦ by rw [ratDirichletChar_eq_conj]; simp)]
  simp [div_eq_mul_inv, mul_comm]

/-- A single local cutoff threshold works for *all* admissible widths and
Sobolev orders at a fixed residue. Under the Montgomery product count its
remaining signed error has the indicated power saving in the modulus. -/
theorem exists_sharpMass_uniform_cylinder_estimate {σ C ε : ℝ} (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (hC : 0 ≤ C) (hn : MontgomeryProductCount σ (montgomeryExponent σ) C) (hε : 0 < ε)
    (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (φ : BruhatCompactSupport Cℚ),
      IsNormalizedCylinder q r H φ → ∀ S₀ : Finset Vℚ,
      ∃ (S : Finset Vℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ), S₀ ⊆ S ∧ LiftAt(φ,S,f) ∧
        ∀ δ > (0 : ℝ), ∀ᶠ R : ℝ in atTop, ∀ {a s : ℝ} (ha : σ-1/2 ≤ a) (hs : 1 < s),
          ‖mass(φ,f,R) - trace((show 0 ≤ a by linarith),hs,φ)‖ ≤ δ + B * (q:ℝ)^(-(1-montgomeryExponent σ)+ε) := by
  obtain ⟨B,hB,hbound⟩ := norm_physicalFull_sub_retained_le hσ hσ1 hC hn hε H hd hc hp
  refine ⟨B,hB,?_⟩
  intro q _ r φ hφ S₀
  obtain ⟨S,f,hS,hf,hlim⟩ := exists_correctedSharpMass_tendsto_fullTrace φ S₀
  rw [wide_eq_full q r H φ hφ] at hlim
  refine ⟨S,f,hS,hf,?_⟩
  intro δ hδ
  filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ] with R hR
  intro a s ha hs
  rw [trace_eq_retained q r H φ hφ]
  rw [dist_eq_norm] at hR
  exact (norm_sub_le_norm_sub_add_norm_sub _ full(q,φ) _).trans
    (add_le_add hR.le (hbound q r a s ha φ hφ))

/-- Paper: §12.3, p. 514. Unconditionally, at each conductor the exact
limiting mean square of the signed local-to-Hilbert errors is the primitive
character mean square divided once more by φ(q). Its numerator is bounded
by a constant times log²(16q), at every strip width including zero. Each
residue has a genuine finite-place lift which works for every width. -/
theorem exists_sharpMass_residue_mean_square (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) (S₀ : Finset Vℚ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q],
      ∃ (φ : (ZMod q)ˣ → BruhatCompactSupport Cℚ) (S : (ZMod q)ˣ → Finset Vℚ)
        (f : (r : (ZMod q)ˣ) → BruhatCompactSupport (SAdeleRing ℚ (S r))ˣ),
        (∀ r, IsNormalizedCylinder q r H (φ r) ∧ S₀ ⊆ S r ∧ LiftAt(φ r,S r,f r)) ∧
        ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
          let D := (∑ χ : DirichletCharacter ℂ q, ‖signedOmittedRow a s H χ‖^2) / q.totient
          Tendsto (fun R : ℝ ↦ ∑ r, ‖mass(φ r,f r,R) - trace(ha,hs,φ r)‖^2) atTop (𝓝 D) ∧
          D ≤ (K*(1+Real.log (16*(q:ℝ))))^2 := by
  obtain ⟨K,hK,hbound⟩ := sum_norm_sq_signedOmitted_le hd hc hp
  refine ⟨K,hK,?_⟩
  intro q _
  let φ (r : (ZMod q)ˣ) := selectedCylinder q r H hd hc
  have hφ (r : (ZMod q)ˣ) := selectedCylinder_spec q r H hd hc
  choose S f hS hf hlocal hgap using
    (fun r : (ZMod q)ˣ ↦ exists_sharpMass_cylinder_signed_comparison q r H hd hc hp (φ r) (hφ r) S₀)
  refine ⟨φ,S,f,fun r ↦ ⟨hφ r,hS r,hf r⟩,?_⟩
  intro a s ha hs D
  have he : ∑ r : (ZMod q)ˣ, ‖cylinderAverage q r (signedOmittedRow a s H)‖^2 = D :=
    sum_norm_sq_cylinderAverage _
  refine ⟨?_,he ▸ hbound q a s⟩
  rw [← he]
  exact tendsto_finsetSum _ fun r _ ↦ ((hgap r ha hs).norm).pow 2

end RiemannMasullo.ConductorCylinder
