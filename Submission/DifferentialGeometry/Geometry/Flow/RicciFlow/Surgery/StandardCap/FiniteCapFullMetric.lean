import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapFullInsertion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteCapWitnessMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev FullMetricE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullMetricE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullMetricE3 target :: scope.openDecls } }
private abbrev FullMetricIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullMetricIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullMetricIC target :: scope.openDecls } }

private theorem pullbackCross_inverse_inner {P S : Type*}
    [TopologicalSpace P] [ChartedSpace FullMetricE3 P] [IsManifold (𝓡 3) ∞ P] [T2Space P]
    [TopologicalSpace S] [ChartedSpace FullMetricE3 S] [IsManifold (𝓡 3) ∞ S]
    (g : SmoothRiemannianMetric (𝓡 3) S) (D : P ≃ₘ⟮𝓡 3, 𝓡 3⟯ S)
    (q : S) (v z : TangentSpace (𝓡 3) q) :
    (Diffeomorph.pullbackMetricCross g D).inner (D.symm q)
      (mfderiv (𝓡 3) (𝓡 3) D.symm q v) (mfderiv (𝓡 3) (𝓡 3) D.symm q z) = g.inner q v z := by
  have he : (D : P → S) ∘ D.symm = id :=
    funext D.apply_symm_apply
  have hcomp := mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) (D.symm q))
    (D.symm.contMDiff.mdifferentiable (by simp) q)
  have hd : (mfderiv (𝓡 3) (𝓡 3) D (D.symm q)).comp (mfderiv (𝓡 3) (𝓡 3) D.symm q) =
      ContinuousLinearMap.id ℝ FullMetricE3 :=
    hcomp.symm.trans ((mfderiv_congr he).trans (by rw [mfderiv_id]; rfl))
  have hv := congrArg (fun F => F v) hd
  have hz := congrArg (fun F => F z) hd
  rw [Diffeomorph.pullbackMetricCross_inner]
  change g.inner (D (D.symm q))
    (mfderiv (𝓡 3) (𝓡 3) D (D.symm q) (mfderiv (𝓡 3) (𝓡 3) D.symm q v))
    (mfderiv (𝓡 3) (𝓡 3) D (D.symm q) (mfderiv (𝓡 3) (𝓡 3) D.symm q z)) = _
  dsimp only [TangentSpace] at hv hz ⊢
  erw [hv, hz, D.apply_symm_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.pullbackCross_inverse_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.pullbackCross_inverse_inner target :: scope.openDecls } }

private local instance fullStaticChartedSpace {B : ℝ} {hB : 0 < B} : ChartedSpace FullMetricE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.fullStaticChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.fullStaticChartedSpace target :: scope.openDecls } }
private local instance fullStaticIsManifold {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.fullStaticIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.fullStaticIsManifold target :: scope.openDecls } }
private local instance fullStaticT2Space {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.fullStaticT2Space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.fullStaticT2Space target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullMetricIC I ∞ (f i))
variable {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [Fact (Module.finrank ℝ F = 3)] [TopologicalSpace K] {J : ModelWithCorners ℝ F K} [J.Boundaryless]
variable [TopologicalSpace N] [ChartedSpace K N] [T2Space N] [IsManifold J ∞ N]
variable {g : SmoothRiemannianMetric J N} {x₀ : N} {δ : ℝ} {k : ℕ}
variable (d : normalizedDatum g x₀ δ k) {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : CanonicalStaticInsertionWitness d A hA D m ε)
variable (b : ι × Bool) (hfit : δ⁻¹ ≤ cuttingCollarWidth (precision b.1))
local notation "FullMetricQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "FullMetricPatch" => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b δ⁻¹

theorem finiteCapFullWitnessMetric_eq :
    let : ChartedSpace FullMetricE3 FullMetricQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullMetricQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    let : T2Space FullMetricQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b δ⁻¹ hfit le_rfl =
      Diffeomorph.pullbackMetricCross w.data.outMetric (finiteCapFullInsertionDiffeomorph I hdim transitionEnd_pos hδ f hf hdisj hs b hfit (inv_pos.mpr d.precision_pos)) := by
  let : ChartedSpace FullMetricE3 FullMetricQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullMetricQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  let : T2Space FullMetricQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  apply SmoothRiemannianMetric.ext_inner
  intro q v z
  rw [Diffeomorph.pullbackMetricCross_inner]
  exact finiteCapWitnessMetric_inner I hdim hδ f hf hdisj hs d w b δ⁻¹ hfit le_rfl q v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_eq

theorem finiteCapFullWitnessMetric_inverse_inner :
    let : ChartedSpace FullMetricE3 FullMetricQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullMetricQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
    let : T2Space FullMetricQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let D := finiteCapFullInsertionDiffeomorph I hdim transitionEnd_pos hδ f hf hdisj hs b hfit (inv_pos.mpr d.precision_pos)
    ∀ (q : InsertionQuotient (inv_pos.mpr d.precision_pos)) (v z : TangentSpace (𝓡 3) q),
      (finiteCapWitnessMetric I hdim hδ f hf hdisj hs d w b δ⁻¹ hfit le_rfl).inner (D.symm q)
        (mfderiv (𝓡 3) (𝓡 3) D.symm q v) (mfderiv (𝓡 3) (𝓡 3) D.symm q z) =
          w.data.outMetric.inner q v z := by
  let : ChartedSpace FullMetricE3 FullMetricQ := finiteCapChartedSpace I hdim transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullMetricQ := finiteCapQuotient_isManifold hdim transitionEnd_pos hδ f hf hdisj hs
  let : T2Space FullMetricQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let D := finiteCapFullInsertionDiffeomorph I hdim transitionEnd_pos hδ f hf hdisj hs b hfit (inv_pos.mpr d.precision_pos)
  dsimp only
  intro q v z
  rw [finiteCapFullWitnessMetric_eq]
  exact pullbackCross_inverse_inner w.data.outMetric D q v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_inverse_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_inverse_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_inverse_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteCapFullWitnessMetric_inverse_inner

end DifferentialGeometry.PDE.RicciFlow.StandardCap
