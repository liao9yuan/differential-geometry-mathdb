import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.Comparison
import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.Distance
import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.WeakDerivative
import Submission.DifferentialGeometry.Topology.Manifold.LocalCompactness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N] [IsManifold I ∞ M] [IsManifold J ∞ N]


abbrev riemannianCurveLength (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ := Geometry.riemannianCurveVariation g γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength

alias regularSpace_of_chartedSpace := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace
alias sigmaCompactSpace_of_chartedSpace := DifferentialGeometry.Topology.Manifold.sigmaCompactSpace_of_chartedSpace

theorem riemannianCurveLength_comp_le (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (f : M → N) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b := by
  exact Geometry.riemannianCurveVariation_comp_le g h f L hf γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le

theorem riemannianCurveLength_mono (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    riemannianCurveLength g γ c d ≤ riemannianCurveLength g γ a b := by
  exact Geometry.riemannianCurveVariation_mono g γ hac hdb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_mono

theorem riemannianCurveLength_comp_le_of_local [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : C(M, N))
    (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b)
    {γ : ℝ → M} {a b : ℝ} (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hfin : riemannianCurveLength g γ a b ≠ ⊤) :
    riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b := by
  exact Geometry.riemannianCurveVariation_comp_le_of_local g h f L hloc hγ hfin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_local ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_comp_le_of_local

theorem riemannianEDistOf_le_riemannianCurveLength
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    riemannianEDistOf g (γ a) (γ b) ≤ riemannianCurveLength g γ a b := by
  exact Geometry.riemannianEDistOf_le_riemannianCurveVariation g γ hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianEDistOf_le_riemannianCurveLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianEDistOf_le_riemannianCurveLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianEDistOf_le_riemannianCurveLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianEDistOf_le_riemannianCurveLength

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_le_pathELength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc a b)) :
    (let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     riemannianCurveLength g γ a b ≤ _root_.Manifold.pathELength I γ a b) := by
  exact Geometry.riemannianCurveVariation_le_pathELength g hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_pathELength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_pathELength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_pathELength ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_le_pathELength

theorem rfs_weak_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M]
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N))
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf h (f y) (f z) ≤ L * riemannianEDistOf g y z)
    (hdf : letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
      ∀ᵐ x ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g),
      MDifferentiableAt I J f x → ∀ v : TangentSpace I x,
        h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤ g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    riemannianCurveLength h (f ∘ γ) a b ≤ riemannianCurveLength g γ a b := by
  exact Geometry.riemannianCurveVariation_comp_le_of_ae_mfderiv g h f hloc hdf γ a b hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_weak_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_weak_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_weak_length ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_weak_length

section CurveLengthVariation

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [RegularSpace M']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_eq_eVariationOn
    (g : SmoothRiemannianMetric I' M') (γ : ℝ → M') (a b : ℝ) :
    riemannianCurveLength g γ a b =
      (letI : _root_.Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E' (TangentSpace I' : M' → Type _) :=
         ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
       letI : PseudoEMetricSpace M' := .ofRiemannianMetric I' M'
       eVariationOn γ (_root_.Set.Icc a b)) := by
  exact Geometry.riemannianCurveVariation_eq_eVariationOn g γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn

end CurveLengthVariation

theorem rfs_local_to_global_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N]
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : RegularSpace N := regularSpace_of_chartedSpace J
  exact Geometry.riemannianEDistOf_comp_le_of_local_riemannianCurveVariation g h f L hloc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length

theorem rfs_local_to_global_length_of_ne_top [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b)
    {x y : M} (hgfin : riemannianEDistOf g x y ≠ ⊤) :
    riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : RegularSpace N := regularSpace_of_chartedSpace J
  exact Geometry.riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_top g h f L hloc hgfin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_top ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_top

theorem rfs_local_to_global_length_of_ne_zero [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0) (hL : L ≠ 0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : RegularSpace N := regularSpace_of_chartedSpace J
  exact Geometry.riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_zero g h f L hL hloc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_zero

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
