import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeRadialCurvature
import Submission.DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import Submission.DifferentialGeometry.Geometry.Metric.Construction.Existence
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local instance modelOneNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedAddCommGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedAddCommGroup
local instance modelOneNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelOneNormedSpace
local instance modelTwoNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedAddCommGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedAddCommGroup
local instance modelTwoNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelTwoNormedSpace

omit [CompleteSpace E] in
theorem modelMetric_form_contDiff (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    ContDiff ℝ ∞ (fun y => tangentBilinearFormToModel y (g.inner y)) := by
  rw [contDiff_clm_apply_iff]
  intro v
  rw [contDiff_clm_apply_iff]
  intro w
  have hfield (a : E) : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (T% (constantModelVectorField (𝕜 := ℝ) a)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (constantModelVectorField v y) (constantModelVectorField w y)) :=
    fun _ => CovariantDerivative.metric_inner_contMDiffAt g
      (hfield v).contMDiffAt (hfield w).contMDiffAt le_rfl
  exact hsmooth.contDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelMetric_form_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelMetric_form_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelMetric_form_contDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelMetric_form_contDiff

omit [CompleteSpace E] in
private theorem modelMetric_nonempty :
    Nonempty (SmoothRiemannianMetric 𝓘(ℝ, E) E) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  obtain ⟨g⟩ := DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric
    (I := 𝓘(ℝ, F)) (M := F)
  exact ⟨Diffeomorph.pullbackMetricCross g (toEuclidean (E := E)).toDiffeomorph⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelMetric_nonempty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelMetric_nonempty target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem exists_modelMetric_extension (U : _root_.TopologicalSpace.Opens E)
    (gU : SmoothRiemannianMetric 𝓘(ℝ, E) U) (x : U) :
    ∃ g : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      ∃ V : _root_.TopologicalSpace.Opens E, ∃ hVU : V ≤ U,
        (x : E) ∈ V ∧ ∀ y : V, ∀ v w : E,
          g.inner (y : E) v w = gU.inner (Opens.inclusion hVU y) v w := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen 𝓘(ℝ, E) U.isOpen)
  obtain ⟨R⟩ := modelMetric_nonempty (E := E)
  obtain ⟨χ, _, hχU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (x : E)).mem_iff.mp
      (U.isOpen.mem_nhds x.2)
  have hχsmooth := χ.contMDiff
  have hχrange : ∀ y : E, χ y ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ => ⟨χ.nonneg, χ.le_one⟩
  let g := R.bumpExtendOpen U gU χ hχsmooth hχrange hχU
  have hnear : {y : E | y ∈ U ∧ χ y = 1} ∈ 𝓝 (x : E) :=
    Filter.inter_mem (U.isOpen.mem_nhds x.2) χ.eventuallyEq_one
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hnear
  let V : _root_.TopologicalSpace.Opens E := ⟨W, hWopen⟩
  have hVU : V ≤ U := fun y hy => (hWsub hy).1
  refine ⟨g, V, hVU, hxW, ?_⟩
  intro y v w
  exact bumpExtendOpen_eq_gU_on R U gU χ hχsmooth hχrange hχU W
    (fun y hy => (hWsub hy).2) hVU y y.2 v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_modelMetric_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_modelMetric_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_modelMetric_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_modelMetric_extension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [CompleteSpace F] [SigmaCompactSpace M] in
theorem exists_partialDiffeomorph_modelMetric
    (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {x : E} (hx : x ∈ Φ.source) :
    ∃ gE : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      ∃ V : _root_.TopologicalSpace.Opens E, x ∈ V ∧ (V : Set E) ⊆ Φ.source ∧
        ∀ y ∈ V, ∀ v w : E, gE.inner y v w =
          g.inner (Φ y) (mfderiv 𝓘(ℝ, E) J Φ y v)
            (mfderiv 𝓘(ℝ, E) J Φ y w) := by
  let U : _root_.TopologicalSpace.Opens E := ⟨Φ.source, Φ.open_source⟩
  let W : _root_.TopologicalSpace.Opens M := ⟨Φ '' (U : Set E), image_opens_isOpen Φ (Set.Subset.refl _)⟩
  let Ψ : Diffeomorph 𝓘(ℝ, E) J U W ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ (Set.Subset.refl _)
  let gU := Diffeomorph.pullbackMetricCross (g.restrictOpen W) Ψ
  obtain ⟨gE, V, hVU, hxV, heq⟩ := exists_modelMetric_extension U gU ⟨x, hx⟩
  refine ⟨gE, V, hxV, hVU, ?_⟩
  intro y hy v w
  erw [heq ⟨y, hy⟩ v w, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  have hd (a : E) : mfderiv 𝓘(ℝ, E) J Ψ (Opens.inclusion hVU ⟨y, hy⟩) a =
      mfderiv 𝓘(ℝ, E) J Φ y a :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      Φ (Set.Subset.refl _) (Opens.inclusion hVU ⟨y, hy⟩) a
  erw [hd, hd]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partialDiffeomorph_modelMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partialDiffeomorph_modelMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partialDiffeomorph_modelMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partialDiffeomorph_modelMetric

theorem metricRm04_partialDiffeomorph_of_inner_eq
    (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)
    (gE : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (V : _root_.TopologicalSpace.Opens E) (hV : (V : Set E) ⊆ Φ.source)
    (hmetric : ∀ y ∈ V, ∀ v w : E, gE.inner y v w =
      g.inner (Φ y) (mfderiv 𝓘(ℝ, E) J Φ y v)
        (mfderiv 𝓘(ℝ, E) J Φ y w))
    (x : V) (a b c d : E) :
    metricRm04StandardAt gE (x : E) a b c d =
      metricRm04StandardAt g (Φ x)
        (mfderiv 𝓘(ℝ, E) J Φ x a) (mfderiv 𝓘(ℝ, E) J Φ x b)
        (mfderiv 𝓘(ℝ, E) J Φ x c) (mfderiv 𝓘(ℝ, E) J Φ x d) := by
  let W : _root_.TopologicalSpace.Opens M := ⟨Φ '' (V : Set E), image_opens_isOpen Φ hV⟩
  let Ψ : Diffeomorph 𝓘(ℝ, E) J V W ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hV
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen 𝓘(ℝ, E) V.isOpen)
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen J W.isOpen)
  have hd (y : V) (v : E) : mfderiv 𝓘(ℝ, E) J Ψ y v =
      mfderiv 𝓘(ℝ, E) J Φ (y : E) v :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hV y v
  have hg : gE.restrictOpen V = Diffeomorph.pullbackMetricCross (g.restrictOpen W) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    erw [SmoothRiemannianMetric.restrictOpen_inner,
      Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      hd, hd]
    exact hmetric y y.2 v w
  have hE := metricRm04StandardAt_restrictOpen gE V x a b c d
  have hM := metricRm04StandardAt_restrictOpen g W (Ψ x)
    (mfderiv 𝓘(ℝ, E) J Ψ x a) (mfderiv 𝓘(ℝ, E) J Ψ x b)
    (mfderiv 𝓘(ℝ, E) J Ψ x c) (mfderiv 𝓘(ℝ, E) J Ψ x d)
  rw [hg] at hE
  have hP := metricRm04Standard_pullbackCross (g.restrictOpen W) Ψ x a b c d
  have hinc (v : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : V → E) x v = v :=
    mfderiv_subtype_val_apply V x v
  rw [hinc, hinc, hinc, hinc] at hE
  simp only [mfderiv_subtype_val_apply] at hM
  have htrans := hE.symm.trans (hP.trans hM)
  change metricRm04StandardAt gE (x : E) a b c d =
    metricRm04StandardAt g (Φ x)
      (mfderiv 𝓘(ℝ, E) J Ψ x a) (mfderiv 𝓘(ℝ, E) J Ψ x b)
      (mfderiv 𝓘(ℝ, E) J Ψ x c) (mfderiv 𝓘(ℝ, E) J Ψ x d) at htrans
  erw [hd, hd, hd, hd] at htrans
  exact htrans

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricRm04_partialDiffeomorph_of_inner_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricRm04_partialDiffeomorph_of_inner_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricRm04_partialDiffeomorph_of_inner_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricRm04_partialDiffeomorph_of_inner_eq

omit [SigmaCompactSpace M] in
theorem exists_concurrentField_partialDiffeomorph
    (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)
    (gE : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (V : _root_.TopologicalSpace.Opens E) (hV : (V : Set E) ⊆ Φ.source)
    (hmetric : ∀ y ∈ V, ∀ v w : E, gE.inner y v w =
      g.inner (Φ y) (mfderiv 𝓘(ℝ, E) J Φ y v)
        (mfderiv 𝓘(ℝ, E) J Φ y w))
    (Z : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : E → Type _))
    (hZ : ∀ y ∈ V, ∀ v : E, metricCov gE Z y v = v) :
    ∃ W : _root_.TopologicalSpace.Opens M, (W : Set M) = Φ '' (V : Set E) ∧
      ∃ ZM : ContMDiffSection J F ∞ (TangentSpace J : W → Type _),
        ∀ y : W, ∀ v : TangentSpace J y,
          metricCov (g.restrictOpen W) ZM y v = v := by
  let W : _root_.TopologicalSpace.Opens M := ⟨Φ '' (V : Set E), image_opens_isOpen Φ hV⟩
  let Ψ : Diffeomorph 𝓘(ℝ, E) J V W ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hV
  let ZV : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : V → Type _) :=
    ⟨restrictOpenTangentField V Z, contMDiff_restrictOpen_section V Z⟩
  have hd (y : V) (v : E) : mfderiv 𝓘(ℝ, E) J Ψ y v =
      mfderiv 𝓘(ℝ, E) J Φ (y : E) v :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hV y v
  have hg : gE.restrictOpen V = Diffeomorph.pullbackMetricCross (g.restrictOpen W) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    erw [SmoothRiemannianMetric.restrictOpen_inner,
      Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      hd, hd]
    exact hmetric y y.2 v w
  refine ⟨W, rfl, pushFwdSectionCross Ψ ZV, ?_⟩
  intro y v
  obtain ⟨x, rfl⟩ := Ψ.surjective y
  let dΨ := Ψ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x
  let a := dΨ.symm v
  have ha : mfderiv 𝓘(ℝ, E) J Ψ x a = v := by
    rw [← Ψ.mfderivToContinuousLinearEquiv_coe
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)]
    exact dΨ.apply_symm_apply v
  have hcov : metricCov (gE.restrictOpen V) ZV x a = a := by
    change metricCov (gE.restrictOpen V) (restrictOpenTangentField V Z) x a = a
    rw [metricCov_restrictOpen_globalSection gE V Z x a]
    exact hZ x x.2 a
  rw [hg] at hcov
  have h := metricCov_pullbackCross (g.restrictOpen W) Ψ ZV x a
  rw [hcov, ha] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_concurrentField_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_concurrentField_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_concurrentField_partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_concurrentField_partialDiffeomorph

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
