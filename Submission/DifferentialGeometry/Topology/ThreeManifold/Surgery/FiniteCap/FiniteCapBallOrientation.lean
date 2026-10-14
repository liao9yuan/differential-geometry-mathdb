import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreOrientation
import Submission.DifferentialGeometry.Topology.Manifold.ClosedBallOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Ball target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E2 target :: scope.openDecls } }
private abbrev ER := E2 × EuclideanSpace ℝ (Fin 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ER
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ER target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IR target :: scope.openDecls } }
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IH target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "OrientedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

private theorem cap_radial_mfderiv (b : ι × Bool) (x : Ball L) :
    letI := closedBallChartedSpace hL
    let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3) x =
      (mfderiv (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
        (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩ :
          finiteCapNeighborhoodOpens hL hδ f hf hdisj b)).comp
      (mfderiv (𝓡∂ 3) (𝓡 3)
        (fun y : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) x) := by
  let := closedBallChartedSpace hL
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let N := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let j : Ball L → OrientedQ := fun y => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩
  let r : Ball L → N := fun y => ⟨j y, Or.inl ⟨y, rfl⟩⟩
  let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
  have hr : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ r :=
    (ContMDiff.subtypeVal_comp_iff N r).mp
      (finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b).contMDiff
  have hC := finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b
  have hmap : C ∘ r = (Subtype.val : Ball L → E3) := by
    funext y
    exact finiteCapNeighborhoodHomeomorph_cap hL hδ f hf hdisj b y
  let D : (Ball L → E3) → (E3 →L[ℝ] E3) := fun g => mfderiv (𝓡∂ 3) (𝓡 3) g x
  have hd : (mfderiv (𝓡∂ 3) (𝓡 3) (C ∘ r) x : E3 →L[ℝ] E3) =
      mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3) x := congrArg D hmap
  have hc : (mfderiv (𝓡∂ 3) (𝓡 3) (C ∘ r) x : E3 →L[ℝ] E3) =
      (mfderiv (𝓡 3) (𝓡 3) C (r x)).comp (mfderiv (𝓡∂ 3) (𝓡 3) r x) :=
    mfderiv_comp (f := r) (g := C) x (hC.mdifferentiableAt (by simp)) (hr.mdifferentiableAt (by simp))
  have hj : (mfderiv (𝓡∂ 3) (𝓡 3) r x : E3 →L[ℝ] E3) = mfderiv (𝓡∂ 3) (𝓡 3) j x :=
    (mfderiv_comp_open_val (𝓡∂ 3) (𝓡 3) N r hr x).symm
  exact hd.symm.trans (hc.trans
    (congrArg (fun A : E3 →L[ℝ] E3 => (mfderiv (𝓡 3) (𝓡 3) C (r x)).comp A) hj))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cap_radial_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.cap_radial_mfderiv target :: scope.openDecls } }

theorem exists_finiteCapSmoothOrientation_preserving_core_and_caps (o : SmoothOrientation I M) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    ∃ oE : (ι × Bool) → Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      ∃ oQ : SmoothOrientation (𝓡 3) OrientedQ,
        (∀ b, oE b = (Module.finBasis ℝ E3).orientation ∨ oE b = -(Module.finBasis ℝ E3).orientation) ∧
        (∀ b : ι × Bool,
          letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
          letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
          ∀ q : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)),
            (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) (oE b)).val q =
              (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q) ∧
        (∀ p : finiteCoreInteriorOpens hL hδ f hf hdisj,
          oQ.val p.val = (finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val p) ∧
        (∀ (b : ι × Bool) (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b),
          oQ.val p.val = (finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b (oE b)).val p) ∧
        (∀ p : cutCore f,
          tangentOrientationEquiv (differentialEquivOfBijective IR (𝓡 3)
            (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
            (finiteCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs) p).toLinearEquiv
              ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p) =
                oQ.val (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p) ) ∧
        ∀ (b : ι × Bool) (x : Ball L),
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
            (fun y : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩)
            (finiteCapInclusion_ball_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) x).toLinearEquiv
              ((closedBallSmoothOrientation hL (oE b)).val x) =
                oQ.val (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  obtain ⟨oE, oQ, hsign, hcollar, hOld, hCap, hCore⟩ :=
    exists_finiteCapSmoothOrientation_preserving_core I hdim hL hδ f hf hdisj hs o
  refine ⟨oE, oQ, hsign, hcollar, hOld, hCap, hCore, ?_⟩
  intro b x
  let j : Ball L → OrientedQ := fun y => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩
  let pN : finiteCapNeighborhoodOpens hL hδ f hf hdisj b := ⟨j x, Or.inl ⟨x, rfl⟩⟩
  let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
  let eJ : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) j
    (finiteCapInclusion_ball_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) x
  let eC : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡 3) (𝓡 3) C
    (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) pN
  let eA : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (closedBall_inclusion_mfderiv_bijective hL) x
  let OB := (closedBallSmoothOrientation hL (oE b)).val x
  have hD : eA = eJ.trans eC := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun D : E3 →L[ℝ] E3 => D v) (cap_radial_mfderiv I hdim hL hδ f hf hdisj hs b x)
  have hA : tangentOrientationEquiv eA.toLinearEquiv OB = oE b :=
    closedBallSmoothOrientation_pushforward hL (oE b) x
  have hQ : tangentOrientationEquiv eC.toLinearEquiv (oQ.val (j x)) = oE b :=
    (congrArg (tangentOrientationEquiv eC.toLinearEquiv) (hCap b pN)).trans
      (finiteCapNeighborhoodSmoothOrientation_pushforward I hdim hL hδ f hf hdisj hs b (oE b) pN)
  apply (tangentOrientationEquiv eC.toLinearEquiv).injective
  calc
    tangentOrientationEquiv eC.toLinearEquiv (tangentOrientationEquiv eJ.toLinearEquiv OB) =
        tangentOrientationEquiv eA.toLinearEquiv OB := by
      rw [hD]
      exact (tangentOrientationEquiv_trans eJ.toLinearEquiv eC.toLinearEquiv OB).symm
    _ = oE b := hA
    _ = tangentOrientationEquiv eC.toLinearEquiv (oQ.val (j x)) := hQ.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation_preserving_core_and_caps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation_preserving_core_and_caps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation_preserving_core_and_caps ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation_preserving_core_and_caps

end DifferentialGeometry.Topology.ThreeManifold.Surgery
