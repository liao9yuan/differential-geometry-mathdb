import Submission.DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSliceManifold
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.NormalFrames
import Mathlib.Analysis.Normed.Operator.Banach

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {S : Set M} {d : ℕ}

private instance tangentFinite (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.tangentFinite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.tangentFinite target :: scope.openDecls } }

theorem embeddedSlice_inclusion_mfderiv_injective
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    Function.Injective (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p) := by
  let _ := embeddedSliceChartedSpace hS
  let L := (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).toLinearMap
  change Function.Injective L
  have hrange : Module.finrank ℝ L.range = d := by
    change Module.finrank ℝ
      (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range = d
    rw [embeddedSlice_inclusion_range_mfderiv hS p, finrank_sliceTangent hS p.2]
  have hsource : Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin d → ℝ) p) = d := by
    change Module.finrank ℝ (Fin d → ℝ) = d
    simp
  have hker : Module.finrank ℝ L.ker = 0 := by
    have hsum := L.finrank_range_add_finrank_ker
    rw [hrange, hsource] at hsum
    omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.embeddedSlice_inclusion_mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.embeddedSlice_inclusion_mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.embeddedSlice_inclusion_mfderiv_injective ``Submission.DifferentialGeometry.Geometry.Topology.embeddedSlice_inclusion_mfderiv_injective

variable [IsManifold I ∞ M]

def normalSplitting (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    (TangentSpace 𝓘(ℝ, Fin d → ℝ) p × normalSpace (I := I) g S p.1) ≃L[ℝ]
      TangentSpace I p.1 := by
  let _ := embeddedSliceChartedSpace hS
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, Fin d → ℝ) p) :=
    inferInstanceAs (NormedAddCommGroup (Fin d → ℝ))
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, Fin d → ℝ) p) :=
    inferInstanceAs (NormedSpace ℝ (Fin d → ℝ))
  let : NormedAddCommGroup (TangentSpace I p.1) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I p.1) := inferInstanceAs (NormedSpace ℝ E)
  let L := mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
  have hcompl : IsCompl L.range (normalSpace (I := I) g S p.1) := by
    change IsCompl
      (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range
      (normalSpace (I := I) g S p.1)
    rw [embeddedSlice_inclusion_range_mfderiv hS p, isCompl_iff, disjoint_iff, codisjoint_iff]
    exact ⟨sliceTangent_inf_normalSpace (I := I) g S p.1,
      sliceTangent_sup_normalSpace (I := I) g S p.1⟩
  have hker : L.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (embeddedSlice_inclusion_mfderiv_injective hS p)
  exact ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl
    (𝕜 := ℝ) (E := TangentSpace 𝓘(ℝ, Fin d → ℝ) p) (F := TangentSpace I p.1)
    (G := normalSpace (I := I) g S p.1) L hcompl hker

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalSplitting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalSplitting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalSplitting ``Submission.DifferentialGeometry.Geometry.Topology.normalSplitting

@[simp] theorem normalSplitting_apply (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    ∀ (a : TangentSpace 𝓘(ℝ, Fin d → ℝ) p) (n : normalSpace (I := I) g S p.1),
      normalSplitting g hS p (a, n) =
        mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p a + n.1 := by
  let _ := embeddedSliceChartedSpace hS
  change ∀ (a : TangentSpace 𝓘(ℝ, Fin d → ℝ) p) (n : normalSpace (I := I) g S p.1),
    normalSplitting g hS p (a, n) =
      mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p a + n.1
  intro a n
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalSplitting_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalSplitting_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalSplitting_apply ``Submission.DifferentialGeometry.Geometry.Topology.normalSplitting_apply

end DifferentialGeometry.Geometry.Topology
