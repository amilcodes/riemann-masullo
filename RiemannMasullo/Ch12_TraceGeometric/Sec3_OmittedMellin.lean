module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_MovingPrimeTrace
import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumCesaro
import RiemannMasullo.ForMathlib.Analysis.Fourier.SparseLaplaceProbe
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-! # Which omitted zeta samples survive the critical detector

Endpoint Abel uniqueness forces every missing right-hand coefficient of a
fixed probe to vanish. On the other side of the center, absolute summability
uniformly bounds the translated series on the positive half-line. -/

@[expose] public noncomputable section
open Classical Filter Function MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.RationalWidthLoss
set_option quotPrecheck false

local notation "Z" => {ρ : ℂ // 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ}
local notation "r(" ρ ")" => (MeromorphicOn.divisor completedRiemannZeta univ (ρ : Z).val).toNat
local notation "w(" ρ ")" => ((ρ : Z).val - (1/2 : ℂ))
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "shift(" H ", " y ")" => (fun x : ℝ ↦ (H : ℝ → ℂ) (x-y))

/-- Missing order at a completed zeta zero on the degree-three strip. -/
def omittedOrder (a : ℝ) (ρ : Z) : ℕ :=
  r(ρ) - spectralStripMultiplicity a 3 (ρ.val.re-1/2) (r(ρ))

/-- Signed contribution of the omitted zeta orders to a translated probe. -/
def omittedMellinTrace (a : ℝ) (H : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∑' ρ : Z, V * ((omittedOrder a ρ : ℂ) * bilateralLaplace shift(H,y) w(ρ))

theorem normOneVolume_ne_zero : V ≠ 0 := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  apply Complex.ofReal_ne_zero.mpr
  apply (ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr ?_).ne' ENNReal.ofReal_ne_top).ne'
  have := NumberField.Units.regulator_pos ℚ
  have := NumberField.classNumber_pos ℚ
  have := NumberField.Units.torsionOrder_pos ℚ
  have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr ℚ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero ℚ))
  positivity

private theorem shifted_discrete (z : ℂ) : ∀ᶠ u in 𝓝[≠] z, u ∉ range (fun ρ : Z ↦ w(ρ)) := by
  have hD := (MeromorphicOn.divisor completedRiemannZeta univ).eq_zero_codiscreteWithin
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hD) (z+1/2) (mem_univ _)
  rw [compl_univ,union_empty] at h
  have ht : Tendsto (fun u : ℂ ↦ u+1/2) (𝓝[≠] z) (𝓝[≠] (z+1/2)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact fun he ↦ hu (add_right_cancel he)
  filter_upwards [ht.eventually h] with u hu
  rintro ⟨ρ,rfl⟩
  change MeromorphicOn.divisor completedRiemannZeta univ (w(ρ)+1/2) = 0 at hu
  rw [sub_add_cancel] at hu
  exact (ne_of_gt ρ.property) hu

private theorem shifted_re_lt (ρ : Z) : w(ρ).re < 1/2 := by
  have hz : ρ.val ∈ zeroSites := by
    change 0 < MeromorphicOn.divisor _ _ _
    rw [principal_divisor_eq_completedRiemannZeta]
    exact ρ.property
  have h := (re_mem_Ioo ⟨ρ.val,hz⟩).2
  change ρ.val.re < 1 at h
  rw [Complex.sub_re]; norm_num; linarith

local notation "coef(" a ", " H ", " ρ ")" => V * ((omittedOrder a ρ : ℂ) * bilateralLaplace H w(ρ))

private theorem summable_coeff (a : ℝ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (hs : tsupport H ⊆ Ioi 0) : Summable (fun ρ : Z ↦ coef(a,H,ρ)) := by
  have h := (hasSum_zetaZeros_centeredVonMangoldt H hH hc hs).summable.norm
  apply Summable.of_norm_bounded (h.mul_left ‖V‖)
  intro ρ
  rw [norm_mul,norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (r(ρ)) _) (norm_nonneg _)) (norm_nonneg _)

private theorem moving_hasSum {a : ℝ} {H : ℝ → ℂ} (hs : Summable (fun ρ : Z ↦ coef(a,H,ρ)))
    {y : ℝ} (hy : 0 ≤ y) :
    HasSum (fun ρ : Z ↦ coef(a,H,ρ)*Complex.exp (w(ρ)*y)) (omittedMellinTrace a H y) := by
  have h : Summable (fun ρ : Z ↦ coef(a,H,ρ)*Complex.exp (w(ρ)*y)) := by
    apply Summable.of_norm_bounded (hs.norm.mul_right (Real.exp (1/2*y)))
    intro ρ
    rw [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (shifted_re_lt ρ).le hy)) (norm_nonneg _)
  convert h.hasSum using 1
  unfold omittedMellinTrace
  apply tsum_congr
  intro ρ
  rw [SparseLaplace.bilateralLaplace_translate]
  ring

/-- After normalization by the polar exponential, the entire omitted trace
decays to zero. No uniform zero-free strip near the pole is needed. -/
theorem tendsto_pole_normalized_omitted (a : ℝ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    Tendsto (fun y : ℝ ↦ (Real.exp (-y/2):ℂ)*omittedMellinTrace a H y) atTop (𝓝 0) := by
  let b (ρ : Z) := coef(a,H,ρ)
  let f (y : ℝ) (ρ : Z) := b ρ * Complex.exp ((w(ρ)-1/2)*y)
  have hs : Summable b := summable_coeff a H hH hc hp
  have hn (y : ℝ) (ρ : Z) : ‖Complex.exp ((w(ρ)-1/2)*y)‖ = Real.exp ((w(ρ).re-1/2)*y) := by
    rw [Complex.norm_exp,Complex.mul_re,Complex.sub_re]; norm_num
  have hterm (ρ : Z) : Tendsto (fun y ↦ f y ρ) atTop (𝓝 0) := by
    have hneg := sub_neg.mpr (shifted_re_lt ρ)
    have hzero : Tendsto (fun y : ℝ ↦ Complex.exp ((w(ρ)-1/2)*y)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [hn]
      exact Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hneg).mpr
        (show Tendsto (fun y : ℝ ↦ y) atTop atTop from tendsto_id))
    simpa [f] using hzero.const_mul (b ρ)
  have hb : ∀ᶠ y : ℝ in atTop, ∀ ρ, ‖f y ρ‖ ≤ ‖b ρ‖ := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    intro ρ
    rw [show ‖f y ρ‖ = ‖b ρ‖ * Real.exp ((w(ρ).re-1/2)*y) by dsimp only [f]; rw [norm_mul,hn]]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (shifted_re_lt ρ).le) hy))
  have h := tendsto_tsum_of_dominated_convergence (g := fun _ : Z ↦ (0:ℂ)) hs.norm hterm hb
  simp only [tsum_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
  rw [← (moving_hasSum (a := a) (H := H) hs hy).tsum_eq,Complex.ofReal_exp,← tsum_mul_left]
  apply tsum_congr
  intro ρ
  change b ρ * Complex.exp ((w(ρ)-1/2)*y) = Complex.exp _ * (b ρ * Complex.exp (w(ρ)*y))
  rw [mul_left_comm,← Complex.exp_add]
  push_cast
  congr 2
  ring

/-- The detector sees precisely the missing right-hand orders on which the
fixed test has nonzero Mellin sample. Every omitted left-hand site gives an
absolutely integrable contribution, even for arbitrarily small positive widths. -/
theorem integrable_omitted_iff_right_samples {a : ℝ} (ha : 0 < a)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hk : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ)*omittedMellinTrace a H y) (Ioi 0) ↔
      ∀ ρ : Z, 1/2 < ρ.val.re → 0 < omittedOrder a ρ → bilateralLaplace H w(ρ) = 0 := by
  let b (ρ : Z) := coef(a,H,ρ)
  have hs : Summable b := summable_coeff a H hH hk hp
  have series := fun y (hy : 0 ≤ y) ↦ moving_hasSum (a := a) (H := H) hs hy
  have hr (ρ : Z) : w(ρ).re = ρ.val.re-1/2 := by norm_num
  constructor
  · intro hi ρ hρ hm
    have hc : a/2 ≤ w(ρ).re := by
      rw [hr]
      by_contra! hb
      have hmid : ρ.val.re-1/2 ∈ Ioo (-a) a := ⟨by linarith,by linarith⟩
      rw [omittedOrder,spectralStripMultiplicity_interior hmid,Nat.sub_self] at hm
      exact (Nat.lt_irrefl 0) hm
    have hnorm : IntegrableOn (fun y : ℝ ↦ ‖omittedMellinTrace a H y‖ * Real.exp (-(a/2)*y)) (Ioi 0) := by
      apply hi.norm.congr
      filter_upwards with y
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
        show -a*y/2 = -(a/2)*y by ring,mul_comm]
    have hzero := eq_zero_of_hasSum_exp_of_endpoint_integrable (fun ρ : Z ↦ w(ρ)) b
      (fun _ _ he ↦ Subtype.ext (sub_left_inj.mp he)) shifted_discrete (fun ρ ↦ (shifted_re_lt ρ).le) hs _ series hnorm ρ hc
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left normOneVolume_ne_zero)).resolve_left
      (by exact_mod_cast (Nat.ne_of_gt hm))
  · intro hann
    have hbound (ρ : Z) (y : ℝ) (hy : 0 ≤ y) : ‖b ρ*Complex.exp (w(ρ)*y)‖ ≤ ‖b ρ‖ := by
      by_cases hb : b ρ = 0
      · simp [hb]
      have hnon : w(ρ).re ≤ 0 := by
        by_contra! hpos
        have horder : 0 < omittedOrder a ρ := by
          by_contra! he
          exact hb (by simp [b,Nat.eq_zero_of_le_zero he])
        exact hb (by dsimp only [b]; rw [hann ρ (by linarith [hr ρ]) horder,mul_zero,mul_zero])
      rw [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      apply mul_le_of_le_one_right (norm_nonneg _)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hnon hy)
    let S (y : ℝ) := ∑' ρ : Z, b ρ*Complex.exp (w(ρ)*(max y 0 : ℝ))
    have hS : Continuous S := continuous_tsum (fun ρ ↦ by fun_prop) hs.norm
      fun ρ y ↦ hbound ρ _ (le_max_right _ _)
    have hEq {y : ℝ} (hy : 0 ≤ y) : S y = omittedMellinTrace a H y := by
      simpa only [S,max_eq_left hy] using (series y hy).tsum_eq
    have hB (y : ℝ) : ‖S y‖ ≤ ∑' ρ, ‖b ρ‖ :=
      tsum_of_norm_bounded hs.norm.hasSum (fun ρ ↦ hbound ρ _ (le_max_right _ _))
    have hi : IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ)*S y) (Ioi 0) := by
      apply ((integrableOn_exp_mul_Ioi (a := -a/2) (by linarith) 0).mul_const (∑' ρ, ‖b ρ‖)).mono'
      · exact (((by fun_prop : Continuous (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ)))).mul hS).aestronglyMeasurable
      filter_upwards with y
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
        show -a*y/2 = -a/2*y by ring]
      exact mul_le_mul_of_nonneg_left (hB y) (Real.exp_pos _).le
    exact hi.congr ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono fun y hy ↦ congrArg (fun z : ℂ ↦ (Real.exp (-a*y/2):ℂ)*z) (hEq (le_of_lt hy)))

end RiemannMasullo.RationalWidthLoss
