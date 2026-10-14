import Batteries.Tactic.Alias
import Submission.DifferentialGeometry.Geometry.Submanifold.IsometricImmersion
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry

section CurvewiseSecondFundamentalForm

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NeZero (Module.finrank ℝ EN)]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def covariantAcceleration
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (t : ℝ) :
    TangentSpace I (gamma t) :=
  covDerivAlong (I := I) g gamma
    (fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s : ℝ →L[ℝ] _) (1 : ℝ)) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.covariantAcceleration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.covariantAcceleration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.covariantAcceleration ``Submission.DifferentialGeometry.Geometry.covariantAcceleration

omit [NeZero (Module.finrank ℝ E)] in
@[simp]
theorem covariantAcceleration_def
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (t : ℝ) :
    covariantAcceleration (I := I) g gamma t =
      covDerivAlong (I := I) g gamma
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s : ℝ →L[ℝ] _) (1 : ℝ)) t :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.covariantAcceleration_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.covariantAcceleration_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.covariantAcceleration_def ``Submission.DifferentialGeometry.Geometry.covariantAcceleration_def

def secondFundamentalFormDiagonalAlongCurve
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M)
    (gamma : ℝ → N) (t : ℝ) : TangentSpace I (iota (gamma t)) :=
  covariantAcceleration (I := I) gM (fun s => iota (gamma s)) t -
    mfderiv IN I iota (gamma t) (covariantAcceleration (I := IN) gN gamma t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve ``Submission.DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
@[simp]
theorem secondFundamentalFormDiagonalAlongCurve_def
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M)
    (gamma : ℝ → N) (t : ℝ) :
    secondFundamentalFormDiagonalAlongCurve gN gM iota gamma t =
      covariantAcceleration (I := I) gM (fun s => iota (gamma s)) t -
        mfderiv IN I iota (gamma t)
          (covariantAcceleration (I := IN) gN gamma t) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve_def ``Submission.DifferentialGeometry.Geometry.secondFundamentalFormDiagonalAlongCurve_def

def hasVanishingSecondFundamentalFormAlongCurves
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) : Prop :=
  ∀ (gamma : ℝ → N) (t : ℝ),
    ContMDiff 𝓘(ℝ, ℝ) IN ∞ gamma →
      secondFundamentalFormDiagonalAlongCurve gN gM iota gamma t = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves ``Submission.DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves

namespace hasVanishingSecondFundamentalFormAlongCurves

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem covariantAcceleration_comp
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : hasVanishingSecondFundamentalFormAlongCurves gN gM iota)
    (gamma : ℝ → N) (t : ℝ)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) IN ∞ gamma) :
    covariantAcceleration (I := I) gM (fun s => iota (gamma s)) t =
      mfderiv IN I iota (gamma t)
        (covariantAcceleration (I := IN) gN gamma t) := by
  exact sub_eq_zero.mp (h gamma t hgamma)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.covariantAcceleration_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.covariantAcceleration_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.covariantAcceleration_comp ``Submission.DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.covariantAcceleration_comp

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem hasGeodesicEquationAt_comp
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : hasVanishingSecondFundamentalFormAlongCurves gN gM iota)
    (hiota : ContMDiff IN I ∞ iota)
    {gamma : ℝ → N} (hgamma : ContMDiff 𝓘(ℝ, ℝ) IN ∞ gamma)
    {t : ℝ} (hgeodesic : HasGeodesicEquationAt (I := IN) gN gamma t) :
    HasGeodesicEquationAt (I := I) gM (iota ∘ gamma) t := by
  have hsource : covariantAcceleration (I := IN) gN gamma t = 0 :=
    (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := IN) gN gamma t hgamma).2 hgeodesic
  have htargetSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (iota ∘ gamma) :=
    hiota.comp hgamma
  change HasGeodesicEquationAt (I := I) gM (fun s => iota (gamma s)) t
  change ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun s => iota (gamma s)) at htargetSmooth
  apply (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
    (I := I) gM (fun s => iota (gamma s)) t htargetSmooth).1
  rw [← covariantAcceleration_def,
    h.covariantAcceleration_comp gamma t hgamma, hsource, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.hasGeodesicEquationAt_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.hasGeodesicEquationAt_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.hasGeodesicEquationAt_comp ``Submission.DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.hasGeodesicEquationAt_comp

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem isGeodesic_comp
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : hasVanishingSecondFundamentalFormAlongCurves gN gM iota)
    (hiota : ContMDiff IN I ∞ iota)
    {gamma : ℝ → N} (hgamma : ContMDiff 𝓘(ℝ, ℝ) IN ∞ gamma)
    (hgeodesic : IsGeodesic (I := IN) gN gamma) :
    IsGeodesic (I := I) gM (iota ∘ gamma) := by
  change IsGeodesic (I := I) gM (fun s => iota (gamma s))
  exact fun t => h.hasGeodesicEquationAt_comp hiota hgamma (hgeodesic t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.isGeodesic_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.isGeodesic_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.isGeodesic_comp ``Submission.DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.isGeodesic_comp

end hasVanishingSecondFundamentalFormAlongCurves

omit [NeZero (Module.finrank ℝ E)] in
theorem hasVanishingSecondFundamentalFormAlongCurves_id
    (g : SmoothRiemannianMetric I M) :
    hasVanishingSecondFundamentalFormAlongCurves g g (id : M → M) := by
  intro gamma t _hgamma
  simp [secondFundamentalFormDiagonalAlongCurve]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves_id ``Submission.DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves_id

end CurvewiseSecondFundamentalForm

section GermInRange

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [CompactSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
    Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_unit_speed_geodesic_germ_in_range_of_vanishingSecondFundamentalForm
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M)
    (hisom : IsRiemannianIsometricImmersion gN gM iota)
    (hII : hasVanishingSecondFundamentalFormAlongCurves gN gM iota)
    (hdim : 0 < Module.finrank ℝ EN) (y : N) :
    ∃ alpha : ℝ → M,
      alpha 0 = iota y ∧
        isUnitSpeedGeodesicGermIn gM (Set.range iota) alpha := by
  classical
  let _ : CompleteSpace EN := FiniteDimensional.complete ℝ EN
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ EN) := ⟨Nat.ne_of_gt hdim⟩
  let _ : IsManifold IN 1 N :=
    IsManifold.of_le (I := IN) (M := N) (n := (∞ : WithTop ℕ∞)) (by decide)
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace IN N
  let _ : T3Space N := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun x : N => TangentSpace IN x) :=
    ⟨gN.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle EN (fun x : N => TangentSpace IN x) :=
    ⟨⟨gN.inner, gN.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let hcompactN : CompactSpace N := inferInstance
  let _ : EMetricSpace N := EMetricSpace.ofRiemannianMetric IN N
  let _ : PseudoEMetricSpace N :=
    (EMetricSpace.ofRiemannianMetric IN N).toPseudoEMetricSpace
  let _ : CompactSpace N := hcompactN
  let _ : CompleteSpace N := complete_of_compact
  let hEnormN : IsMetricNorm (I := IN) (M := N) gN :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := IN) gN x v
  obtain ⟨w, hw⟩ := exists_unit_tangent_of_finrank_pos gN hdim y
  let gamma : ℝ → N := intrinsicGeodesic (I := IN) gN hEnormN y w
  have hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) IN ∞ gamma :=
    intrinsicGeodesic_contMDiff (I := IN) gN hEnormN y w
  have hgammaGeodesic : IsGeodesic (I := IN) gN gamma :=
    intrinsicGeodesic_isGeodesic (I := IN) gN hEnormN y w
  have hgammaZero : gamma 0 = y :=
    intrinsicGeodesic_zero (I := IN) gN hEnormN y w
  have hgammaVelocity :
      (mfderiv 𝓘(ℝ, ℝ) IN gamma 0 (1 : ℝ) : EN) = (w : EN) :=
    intrinsicGeodesic_mfderiv_zero (I := IN) gN hEnormN y w
  have hgammaUnit : ∀ t : ℝ,
      gN.inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) IN gamma t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) IN gamma t (1 : ℝ)) = 1 := by
    intro t
    exact (intrinsicGeodesic_speedSq_eq (I := IN) gN hEnormN y w t).trans hw
  let beta : ℝ → M := fun t => iota (gamma t)
  have hbetaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ beta := by
    change ContMDiff 𝓘(ℝ, ℝ) I ∞ (iota ∘ gamma)
    exact hisom.contMDiff.comp hgammaSmooth
  have hbetaGeodesic : IsGeodesic (I := I) gM beta := by
    change IsGeodesic (I := I) gM (iota ∘ gamma)
    exact hII.isGeodesic_comp hisom.contMDiff hgammaSmooth hgammaGeodesic
  have hbetaZero : beta 0 = iota y := by
    change iota (gamma 0) = iota y
    rw [hgammaZero]
  let v : TangentSpace I (iota y) := mfderiv IN I iota y w
  have hbetaVelocity :
      (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ) : E) = (v : E) := by
    have hchain := mfderiv_comp_apply
      (I := 𝓘(ℝ, ℝ)) (I' := IN) (I'' := I) 0
      (hisom.contMDiff.mdifferentiableAt (by simp))
      (hgammaSmooth.mdifferentiableAt (by simp)) (1 : ℝ)
    change mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ) =
      mfderiv IN I iota (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) IN gamma 0 (1 : ℝ)) at hchain
    rw [hchain, hgammaZero]
    exact congrArg (mfderiv IN I iota y) hgammaVelocity
  obtain ⟨alpha, delta, hdelta, halphaZero, halphaVelocity,
      halphaDifferentiable, halphaGeodesicAt⟩ :=
    exists_isGeodesicAt_on_ioo_at_velocity gM (iota y) v
  let U : Set ℝ := Set.Ioo (-delta) delta
  have hzeroU : (0 : ℝ) ∈ U := ⟨neg_lt_zero.mpr hdelta, hdelta⟩
  have halphaContinuous : ContinuousOn alpha U := by
    intro t ht
    exact (halphaDifferentiable t ht).continuousAt.continuousWithinAt
  have halphaGeodesic : IsGeodesicOn (I := I) gM alpha U := by
    intro t ht
    exact (halphaGeodesicAt t ht).hasGeodesicEquationAt gM
  have halphaSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ alpha U :=
    isGeodesicOn_contMDiffOn_infty
      (I := I) gM isOpen_Ioo halphaGeodesic halphaContinuous
  have halphaEqBeta : Set.EqOn alpha beta U := by
    apply geo_eqOn_of_initial (I := I) gM isOpen_Ioo isPreconnected_Ioo hzeroU
      halphaGeodesic (hbetaGeodesic.isGeodesicOn U)
      halphaContinuous hbetaSmooth.continuous.continuousOn
    · exact halphaZero.trans hbetaZero.symm
    · exact halphaVelocity.trans hbetaVelocity.symm
  have halphaUnit : ∀ t ∈ U,
      gM.inner (alpha t)
        (mfderiv 𝓘(ℝ, ℝ) I alpha t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I alpha t (1 : ℝ)) = 1 := by
    intro t ht
    have heqGerm : alpha =ᶠ[nhds t] beta :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) halphaEqBeta
    rw [halphaEqBeta ht, heqGerm.mfderiv_eq]
    exact (hisom.speed_sq_comp
      (hgammaSmooth.mdifferentiableAt (by simp))).trans (hgammaUnit t)
  refine ⟨alpha, halphaZero, delta, hdelta,
    halphaGeodesicAt 0 hzeroU, halphaSmooth, halphaGeodesic,
    halphaUnit, ?_⟩
  intro t ht
  rw [halphaEqBeta ht]
  exact ⟨gamma t, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_unit_speed_geodesic_germ_in_range_of_vanishingSecondFundamentalForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_unit_speed_geodesic_germ_in_range_of_vanishingSecondFundamentalForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_unit_speed_geodesic_germ_in_range_of_vanishingSecondFundamentalForm ``Submission.DifferentialGeometry.Geometry.exists_unit_speed_geodesic_germ_in_range_of_vanishingSecondFundamentalForm

end GermInRange

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

@[reducible] alias HasVanishingSecondFundamentalFormAlongCurves := DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves
end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry.HasVanishingSecondFundamentalFormAlongCurves

alias covariantAcceleration_comp := DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.covariantAcceleration_comp
alias hasGeodesicEquationAt_comp := DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.hasGeodesicEquationAt_comp
alias isGeodesic_comp := DifferentialGeometry.Geometry.hasVanishingSecondFundamentalFormAlongCurves.isGeodesic_comp
end DifferentialGeometry.Geometry.HasVanishingSecondFundamentalFormAlongCurves
