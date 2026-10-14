import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionQuotient
import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Filter _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private def centralToOpen (δ : ℝ) (q : neckCentralDomain δ) : openCylinder δ⁻¹ :=
  ⟨q.1.1, q.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.centralToOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.centralToOpen target :: scope.openDecls } }

private theorem centralToOpen_continuousOn (δ : ℝ)
    {a b : ℝ} (γ : ℝ → neckCentralDomain δ)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    ContinuousOn (centralToOpen δ ∘ γ) (_root_.Set.Icc a b) := by
  intro t ht
  change _root_.Filter.Tendsto (centralToOpen δ ∘ γ) (𝓝[_root_.Set.Icc a b] t)
    (𝓝 (centralToOpen δ (γ t)))
  rw [tendsto_subtype_rng]
  have hneck : ContinuousOn (fun s => ((γ s).1 : neckBuffer δ)) (_root_.Set.Icc a b) :=
    continuous_subtype_val.comp_continuousOn hγ
  have hpair : ContinuousOn (fun s => (((γ s).1 : neckBuffer δ) : NeckCylinder)) (_root_.Set.Icc a b) :=
    continuous_subtype_val.comp_continuousOn hneck
  exact hpair t ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.centralToOpen_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.centralToOpen_continuousOn target :: scope.openDecls } }

private def centralPath {d : normalizedDatum g x₀ δ k}
    (γ : ℝ → neckCentralDomain δ) : ℝ → d.oriented.controlledImage :=
  fun t => ⟨d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩),
    d.oriented.controlledMap_mem_controlledImage _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.centralPath
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.centralPath target :: scope.openDecls } }

private theorem centralPath_continuousOn {d : normalizedDatum g x₀ δ k}
    {a b : ℝ} (γ : ℝ → neckCentralDomain δ)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    ContinuousOn (centralPath (d := d) γ) (_root_.Set.Icc a b) := by
  have hraw : ContinuousOn (d.oriented.controlledMap ∘ centralToOpen δ ∘ γ)
      (_root_.Set.Icc a b) :=
    (d.oriented.controlledMap_smooth.continuous).comp_continuousOn
      (centralToOpen_continuousOn δ γ hγ)
  intro t ht
  change _root_.Filter.Tendsto (centralPath (d := d) γ) (𝓝[_root_.Set.Icc a b] t)
    (𝓝 (centralPath γ t))
  rw [tendsto_subtype_rng]
  exact hraw t ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.centralPath_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.centralPath_continuousOn target :: scope.openDecls } }

private theorem centralPath_val_eq {d : normalizedDatum g x₀ δ k}
    (γ : ℝ → neckCentralDomain δ) :
    (Subtype.val ∘ centralPath (d := d) γ) =
      (fun t => d.oriented.map (γ t).1) := by
  funext t
  change d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩) = d.oriented.map (γ t).1
  rw [d.oriented.controlledMap_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.centralPath_val_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.centralPath_val_eq target :: scope.openDecls } }

theorem CanonicalStaticInsertionWitness.collapse_length_of_toNormalizedNeck
    {d : normalizedDatum g x₀ δ k}
    {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (γ : ℝ → neckCentralDomain δ) (a b : ℝ)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    DifferentialGeometry.Geometry.riemannianCurveVariation w.data.outMetric
        (w.data.collapse ∘ (fun t =>
          (⟨d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩),
            d.oriented.controlledMap_mem_controlledImage _⟩ : d.oriented.controlledImage))) a b ≤
      DifferentialGeometry.Geometry.riemannianCurveVariation g
        (fun t => d.oriented.map (γ t).1) a b := by
  let : RegularSpace M := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace I
  have hp := w.properties.collapse_length (centralPath (d := d) γ) a b
    (centralPath_continuousOn (d := d) γ hγ)
  rw [DifferentialGeometry.Geometry.riemannianCurveVariation_restrictOpen g
    d.oriented.controlledImage (centralPath (d := d) γ) a b
    (centralPath_continuousOn (d := d) γ hγ)] at hp
  rw [centralPath_val_eq (d := d) γ] at hp
  have hpath : centralPath (d := d) γ = (fun t =>
      (⟨d.oriented.controlledMap (⟨(γ t).1.1, (γ t).2⟩),
        d.oriented.controlledMap_mem_controlledImage _⟩ : d.oriented.controlledImage)) := by
    rfl
  rw [hpath] at hp
  exact hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length_of_toNormalizedNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length_of_toNormalizedNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length_of_toNormalizedNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length_of_toNormalizedNeck

end DifferentialGeometry.PDE.RicciFlow.StandardCap
