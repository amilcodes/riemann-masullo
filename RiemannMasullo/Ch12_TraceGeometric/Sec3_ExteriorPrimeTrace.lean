module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_PhysicalWindow
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_OmittedMellin
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_MovingPrimeTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec5_SignedTranslateBound
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_WeightedPrimeRemainder
import Mathlib.Tactic

/-! # The signed rational exterior trace and the first prime shell

Use the actual degree-three Sobolev strip and its spectral projection at
the half twist. For each fixed radial probe, the weighted difference on the
strict exterior is integrable precisely when the omitted right-hand zeta
samples vanish. Compact interpolation realizes this on nontrivial probes. -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.RationalWidthLoss

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "mℚ" => (continuousIdeleClassNorm ℚ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "ℓ" => (fun x : Cℚ ↦ Real.log (((mℚ) x).val : ℝ))
local notation "W(" a ")" => CompactIntervalSobolev μℚ ℓ (-(a : ℝ)) a 3
local notation "h₃" => (by norm_num : (0:ℝ) ≤ 3)
local notation "A(" ha ", " φ ")" => hardySobolevTestAction μℚ mℚ _ _ 3 (neg_le_self ha) h₃ φ
local notation "P(" ha ")" => spectralProjection (F := ℚ) (1/2) ha h₃
local notation "L(" ha ", " g ")" => hardySobolevTranslation μℚ mℚ _ _ 3 (neg_le_self ha) h₃ g
local notation "tr(" L ", " T ")" => hilbertTrace (⟨L * (T : nuclearEndomorphisms _).val,
  mul_mem_nuclearEndomorphisms_left L T⟩ : nuclearEndomorphisms _)
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "shift(" H ", " y ")" => (fun x : ℝ ↦ (H : ℝ → ℂ) (x-y))
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x = (H : ℝ → ℂ) (ℓ x)

/-- The continuous rational norm section parametrized by additive log norm. -/
def rationalLogSection (y : ℝ) : Cℚ :=
  QuotientGroup.mk (canonicalIdeleNormSection ℚ (positiveRealLogEquiv.symm (Multiplicative.ofAdd y)))

private theorem section_continuous : Continuous rationalLogSection :=
  continuous_quotient_mk'.comp ((canonicalIdeleNormSection_continuous ℚ).comp
    (positiveRealLogEquiv.symm.continuous.comp continuous_id))

private theorem section_log (y : ℝ) : ℓ (rationalLogSection y) = y := by
  change Real.log (((ideleNorm ℚ (canonicalIdeleNormSection ℚ _)).val : ℝ)) = y
  rw [canonicalIdeleNormSection_rightInverse ℚ,← positiveRealLogEquiv_apply]
  simp

private theorem log_mul (b c : Cℚ) : ℓ (b*c) = ℓ b + ℓ c := by
  dsimp only
  simp only [map_mul,Units.val_mul,NNReal.coe_mul]
  exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

private theorem log_inv_mul (b c : Cℚ) : ℓ (b⁻¹*c) = ℓ c-ℓ b := by
  have h := log_mul b (b⁻¹*c)
  rw [mul_inv_cancel_left] at h
  linarith

theorem rationalLogNorm_measurable : Measurable ℓ :=
  Real.measurable_log.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp (mℚ).continuous)).measurable

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
local notation "AG(" ha ", " φ ")" => hardySobolevTestAction μ m _ _ 3 (neg_le_self ha) h₃ φ
local notation "LG(" ha ", " g ")" => hardySobolevTranslation μ m _ _ 3 (neg_le_self ha) h₃ g

private theorem action_translate_general {a : ℝ} (ha : 0 ≤ a) (g : G) (φ ψ : BruhatCompactSupport G)
    (hψ : ∀ x, ψ.val x = φ.val (g⁻¹*x)) : AG(ha,ψ) = (LG(ha,g)).comp (AG(ha,φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ _).ae_eq
  have hA := hardySobolevTestAction_apply μ m (-a) a 3 (neg_le_self ha) h₃ φ u
  have pre := (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp hA
  filter_upwards [hardySobolevTestAction_apply μ m (-a) a 3 (neg_le_self ha) h₃ ψ u,
    hardySobolevTranslation_apply μ m (-a) a 3 (neg_le_self ha) h₃ g (AG(ha,φ) u),pre] with x ht hL hpre
  change (AG(ha,ψ) u) x = (LG(ha,g) (AG(ha,φ) u)) x
  change (AG(ha,φ) u) (g⁻¹*x) = lcaConvolution μ φ.val u (g⁻¹*x) at hpre
  rw [ht,hL,hpre]
  change (∫ t, ψ.val t * u (t⁻¹*x) ∂μ) = ∫ t, φ.val t * u (t⁻¹*(g⁻¹*x)) ∂μ
  rw [← integral_mul_left_eq_self (fun t ↦ ψ.val t * u (t⁻¹*x)) g]
  simp only [hψ,inv_mul_cancel_left,mul_inv_rev,mul_assoc]

end

/-- Projected convolution on the actual degree-three physical strip Hilbert space. -/
def physicalProjectedTraceOperator {a : ℝ} (ha : 0 ≤ a) (φ : BruhatCompactSupport Cℚ) :
    nuclearEndomorphisms W(a) :=
  ⟨(A(ha,φ)).comp (P(ha)), (stripDiagonal_projective_trace (F := ℚ) ha (by norm_num : (1:ℝ) < 3)
    φ (stripTestAction_spectralProjection_has_projectiveKernel (F := ℚ) (1/2) ha h₃ φ)).choose⟩

private def quotientTraceOperator {a : ℝ} (ha : 0 ≤ a) (φ : BruhatCompactSupport Cℚ) :
    nuclearEndomorphisms (spectralSobolevQuotient ℚ (1/2) (neg_le_self ha) h₃) :=
  ⟨spectralConvolution (F := ℚ) (1/2) (neg_le_self ha) h₃ φ,
    (stripDiagonal_projective_trace (F := ℚ) ha (by norm_num : (1:ℝ)<3)
      φ (stripTestAction_spectralProjection_has_projectiveKernel (F := ℚ) (1/2) ha h₃ φ)).choose_spec.choose⟩

private theorem projected_trace {a : ℝ} (ha : 0 ≤ a) (φ : BruhatCompactSupport Cℚ) :
    hilbertTrace (physicalProjectedTraceOperator ha φ) = hilbertTrace (quotientTraceOperator ha φ) :=
  (stripDiagonal_projective_trace (F := ℚ) ha (by norm_num : (1:ℝ)<3)
    φ (stripTestAction_spectralProjection_has_projectiveKernel (F := ℚ) (1/2) ha h₃ φ)).choose_spec.choose_spec

local notation "hi(" a ", " y ")" => degreeThreeOutputCutoff μℚ mℚ a (measurableSet_lt (measurable_const (a := 3*(y:ℝ)/4)) rationalLogNorm_measurable)

/-- Hilbert trace of the genuine exterior output cutoff on projected convolution
by the translated probe. The strict inequality fixes the boundary convention. -/
def exteriorStripTrace {a : ℝ} (ha : 0 ≤ a) (φ : BruhatCompactSupport Cℚ) (y : ℝ) : ℂ :=
  tr(hi(a,y),physicalProjectedTraceOperator ha (ideleClassBruhatTranslate (rationalLogSection y) φ))

private theorem translated_covariance {a : ℝ} (ha : 0 ≤ a) (φ : BruhatCompactSupport Cℚ) (y : ℝ) :
    (physicalProjectedTraceOperator ha (ideleClassBruhatTranslate (rationalLogSection y) φ)).val =
      L(ha,rationalLogSection y)*(physicalProjectedTraceOperator ha φ).val := by
  let g := rationalLogSection y
  change (A(ha,ideleClassBruhatTranslate g φ)).comp (P(ha)) = _
  rw [action_translate_general μℚ mℚ ha g φ _ (ideleClassBruhatTranslate_apply g φ)]
  rfl

attribute [local irreducible] ideleClassNorm rationalLogSection ideleClassTamagawaMeasure in
set_option maxHeartbeats 600000 in
private theorem spatial_error {a : ℝ} (ha : 0 < a) (φ : BruhatCompactSupport Cℚ) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) * (exteriorStripTrace ha.le φ y -
      hilbertTrace (quotientTraceOperator ha.le (ideleClassBruhatTranslate (rationalLogSection y) φ)))) (Ioi 0) := by
  have hs (y : ℝ) (x : Cℚ) : ℓ (rationalLogSection y*x) = ℓ x+y := by rw [log_mul,section_log,add_comm]
  let T : nuclearEndomorphisms W(a) := physicalProjectedTraceOperator ha.le φ
  let S (y : ℝ) : nuclearEndomorphisms W(a) := physicalProjectedTraceOperator ha.le (ideleClassBruhatTranslate (rationalLogSection y) φ)
  have hS (y : ℝ) : (S y).val = L(ha.le,rationalLogSection y)*T.val := translated_covariance ha.le φ y
  have h₀ := integrable_exterior_sub_full (G := Cℚ) (a := a) μℚ mℚ rationalLogSection section_continuous.measurable
    hs ha
  have h := h₀ T S hS
  apply h.congr
  filter_upwards with y
  change _ * (exteriorStripTrace ha.le φ y - hilbertTrace (physicalProjectedTraceOperator ha.le _)) = _
  rw [projected_trace]

local notation "Z" => {ρ : ℂ // 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ}
local notation "w(" ρ ")" => ((ρ : Z).val - (1/2 : ℂ))

private theorem translate_support {l u y : ℝ} {H : ℝ → ℂ} (hb : tsupport H ⊆ Icc l u) :
    tsupport shift(H,y) ⊆ Icc (l+y) (u+y) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h := hb (subset_tsupport H (show H (x-y) ≠ 0 from hx))
  exact ⟨by linarith [h.1],by linarith [h.2]⟩

private theorem moving_sum {a l u : ℝ} (ha : 0 ≤ a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,H)) {y : ℝ} (hy : 0 ≤ y) :
    HasSum (fun ρ : Z ↦ V * ((omittedOrder a ρ : ℂ) * bilateralLaplace shift(H,y) w(ρ)))
      (V * centeredVonMangoldtValue shift(H,y) -
        hilbertTrace (quotientTraceOperator ha (ideleClassBruhatTranslate (rationalLogSection y) φ))) := by
  have hw := translate_support (y := y) hb
  apply hasSum_centeredVonMangoldt_sub_radialStripTrace shift(H,y) (hH.comp (contDiff_id.sub contDiff_const))
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hw)
    (fun x hx ↦ (by linarith [(hw hx).1] : 0 < x)) _ ?_ ha (by norm_num : (1:ℝ)<3) _ rfl
  intro x
  rw [ideleClassBruhatTranslate_apply,hφ,log_inv_mul,section_log]
  rfl

/-- For *every* fixed radial test supported in a positive log window with vanishing
positive polar moment, the signed exterior/first-prime error plus the explicit
omitted Mellin trace belongs to the critical weighted L¹ space. -/
theorem integrable_exterior_first_add_omitted {a l u : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u)
    (hp : bilateralLaplace H (1/2) = 0) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,H)) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2) : ℂ) *
      (exteriorStripTrace ha.le φ y + V*rationalFirstPrimeSum shift(H,y) + omittedMellinTrace a H y)) (Ioi 0) := by
  have h₁ := (integrable_weighted_centered_add_first ha hl H hH.continuous hb hp).const_mul V
  have h₂ := spatial_error ha φ
  apply (h₁.add h₂).congr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  have hS := (moving_sum ha.le hl H hH hb φ hφ (le_of_lt hy)).tsum_eq
  change omittedMellinTrace a H y = _ at hS
  dsimp only [Pi.add_apply]
  rw [hS]
  ring

/-- The original weighted comparison holds exactly when the explicitly omitted
zeta samples are integrable with that weight. -/
theorem integrable_exterior_first_iff_omitted {a l u : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u)
    (hp : bilateralLaplace H (1/2) = 0) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,H)) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      (exteriorStripTrace ha.le φ y + V*rationalFirstPrimeSum shift(H,y))) (Ioi 0) ↔
      IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ)*omittedMellinTrace a H y) (Ioi 0) := by
  have h := integrable_exterior_first_add_omitted ha hl H hH hb hp φ hφ
  constructor <;> intro hi <;> apply (h.sub hi).congr <;> filter_upwards with y <;> dsimp <;> ring


/-- For a prescribed polar-free test, the physical signed comparison holds
exactly when its Mellin transform kills every missing right-hand zero order. -/
theorem exterior_firstPrime_iff_right_samples {a l u : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u)
    (hp : bilateralLaplace H (1/2) = 0) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,H)) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      (exteriorStripTrace ha.le φ y + V*rationalFirstPrimeSum shift(H,y))) (Ioi 0) ↔
      ∀ ρ : Z, 1/2 < ρ.val.re → 0 < omittedOrder a ρ → bilateralLaplace H w(ρ) = 0 :=
  (integrable_exterior_first_iff_omitted ha hl H hH hb hp φ hφ).trans
    (integrable_omitted_iff_right_samples ha H hH
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb) (fun _ hx ↦ hl.trans_le (hb hx).1))

/-- One compact normalized polar-free probe, with arbitrarily prescribed critical
Mellin samples, matches the first-prime shell on the actual exterior for every
strip width above the prescribed positive threshold. -/
theorem exists_exterior_firstPrime_matching {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ : Injective γ) (v : ι → ℂ) {δ c ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hl : ε < c) :
    ∃ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ),
      ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c-ε) (c+ε) ∧ H c = 1 ∧ radial(φ,H) ∧
      bilateralLaplace H (1/2) = 0 ∧ bilateralLaplace H (-(1/2)) = 0 ∧
      (∀ j, bilateralLaplace H ((γ j : ℂ)*Complex.I) = v j) ∧
      ∀ {a : ℝ} (ha : δ ≤ a), IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
        (exteriorStripTrace (hδ.le.trans ha) φ y + V*rationalFirstPrimeSum shift(H,y))) (Ioi 0) := by
  obtain ⟨H,hH,hb,hc,hp,hm,hv,hz⟩ := exists_polarFree_critical_probe γ hγ v hδ hε c
  obtain ⟨φ,hφ⟩ := exists_normTest (F := ℚ) H hH (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb)
  refine ⟨H,φ,hH,hb,hc,hφ,hp,hm,hv,?_⟩
  intro a ha
  apply (exterior_firstPrime_iff_right_samples (hδ.trans_le ha) (sub_pos.mpr hl) H hH hb hp φ hφ).mpr
  intro ρ hρ horder
  have hsite : ρ.val ∈ zeroSites := by
    change 0 < MeromorphicOn.divisor _ _ _
    rw [principal_divisor_eq_completedRiemannZeta]
    exact ρ.property
  have hδρ : δ ≤ |ρ.val.re-1/2| := by
    rw [abs_of_pos (sub_pos.mpr hρ)]
    by_contra! hsmall
    have hmid : ρ.val.re-1/2 ∈ Ioo (-a) a := ⟨by linarith,by linarith⟩
    rw [omittedOrder,spectralStripMultiplicity_interior hmid,Nat.sub_self] at horder
    exact (Nat.lt_irrefl 0) horder
  exact hz ⟨⟨ρ.val,hsite⟩,hδρ⟩


end RiemannMasullo.RationalWidthLoss
