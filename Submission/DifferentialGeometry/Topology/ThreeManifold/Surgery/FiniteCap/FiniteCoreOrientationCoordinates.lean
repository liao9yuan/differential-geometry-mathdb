import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapLocalOrientations
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInclusionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

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
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
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
local notation "CoreCoordinateQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCoreOldDomainOpens : _root_.TopologicalSpace.Opens (cutCore f) :=
  ⟨(Subtype.val : cutCore f → M) ⁻¹' interior (cutCore f),
    isOpen_interior.preimage continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldDomainOpens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldDomainOpens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldDomainOpens ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldDomainOpens

def finiteCoreOldLift : finiteCoreOldDomainOpens f → finiteCoreInteriorOpens hL hδ f hf hdisj :=
  fun p => ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p.val,
    ⟨p.val, p.property, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift

include hs in
theorem finiteCoreOldLift_contMDiff :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff IR (𝓡 3) ∞ (finiteCoreOldLift hL hδ f hf hdisj) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  apply (ContMDiff.subtypeVal_comp_iff (finiteCoreInteriorOpens hL hδ f hf hdisj)
    (finiteCoreOldLift hL hδ f hf hdisj)).mp
  exact (finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs).contMDiff.comp
    (contMDiff_subtype_val (I := IR) (U := finiteCoreOldDomainOpens f))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_contMDiff

theorem finiteCoreOldLift_ambient_coordinate :
    let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs ∘ finiteCoreOldLift hL hδ f hf hdisj =
      (Subtype.val : cutCore f → M) ∘ (Subtype.val : finiteCoreOldDomainOpens f → cutCore f) := by
  let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  funext p
  let q := finiteCoreOldLift hL hδ f hf hdisj p
  let x := (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm q
  have hx : (⟨x.val, interior_subset x.property⟩ : cutCore f) = p.val :=
    (injective_finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
      (finiteCoreInteriorDiffeomorph_symm_original I hdim hL hδ f hf hdisj hs q)
  exact congrArg Subtype.val hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_coordinate ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_coordinate

theorem finiteCoreOldLift_ambient_mfderiv (p : finiteCoreOldDomainOpens f) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv IR I (Subtype.val : cutCore f → M) p.val =
      (mfderiv (𝓡 3) I (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
        (finiteCoreOldLift hL hδ f hf hdisj p)).comp
      (mfderiv IR (𝓡 3) (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) p.val) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let K := finiteCoreOldDomainOpens f
  let O := finiteCoreInteriorOpens hL hδ f hf hdisj
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let a := (Subtype.val : cutCore f → M)
  let σ := finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs
  let jO := finiteCoreOldLift hL hδ f hf hdisj
  have hj := (finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs).contMDiff
  have ha := (cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs).contMDiff
  have hσ := finiteOldAmbientCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs
  have hjO := finiteCoreOldLift_contMDiff I hdim hL hδ f hf hdisj hs
  have hDj : (mfderiv IR (𝓡 3) jO p : ER →L[ℝ] E3) = mfderiv IR (𝓡 3) j p.val :=
    (mfderiv_comp_open_val IR (𝓡 3) O jO hjO p).symm.trans
      (DifferentialGeometry.mfderiv_restrict_open (I := IR) (J := 𝓡 3) j K p)
  have hcomp : (mfderiv IR I (σ ∘ jO) p : ER →L[ℝ] E) =
      (mfderiv (𝓡 3) I σ (jO p)).comp (mfderiv IR (𝓡 3) jO p) :=
    mfderiv_comp (f := jO) (g := σ) p (hσ.mdifferentiableAt (by simp)) (hjO.mdifferentiableAt (by simp))
  let D : (K → M) → (ER →L[ℝ] E) := fun g => mfderiv IR I g p
  have hd : (mfderiv IR I (σ ∘ jO) p : ER →L[ℝ] E) =
      mfderiv IR I (a ∘ (Subtype.val : K → cutCore f)) p :=
    congrArg D (finiteCoreOldLift_ambient_coordinate I hdim hL hδ f hf hdisj hs)
  have hrestrict : (mfderiv IR I a p.val : ER →L[ℝ] E) =
      mfderiv IR I (a ∘ (Subtype.val : K → cutCore f)) p :=
    (DifferentialGeometry.mfderiv_restrict_open (I := IR) (J := I) a K p).symm
  have hlast : (mfderiv (𝓡 3) I σ (jO p)).comp (mfderiv IR (𝓡 3) jO p) =
      ((mfderiv (𝓡 3) I σ (jO p)).comp (mfderiv IR (𝓡 3) j p.val) : ER →L[ℝ] E) :=
    congrArg (fun A : ER →L[ℝ] E3 => (mfderiv (𝓡 3) I σ (jO p)).comp A) hDj
  exact hrestrict.trans (hd.symm.trans (hcomp.trans hlast))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_mfderiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOldLift_ambient_mfderiv

def finiteCoreCollarLift (b : ι × Bool) :
    S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) → finiteCapNeighborhoodOpens hL hδ f hf hdisj b :=
  fun q => ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q), Or.inr ⟨q, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift

include hs in
theorem finiteCoreCollarLift_contMDiff (b : ι × Bool) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff IR (𝓡 3) ∞ (finiteCoreCollarLift hL hδ f hf hdisj b) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  apply (ContMDiff.subtypeVal_comp_iff (finiteCapNeighborhoodOpens hL hδ f hf hdisj b)
    (finiteCoreCollarLift hL hδ f hf hdisj b)).mp
  exact (finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs).contMDiff.comp
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_contMDiff

theorem finiteCoreCollarLift_radial_coordinate (b : ι × Bool) :
    let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b ∘ finiteCoreCollarLift hL hδ f hf hdisj b =
      radialCollarOrientationMap L (cuttingCollarWidth (precision b.1)) := by
  let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  funext q
  exact finiteCapNeighborhoodHomeomorph_collar hL hδ f hf hdisj b q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_coordinate ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_coordinate

theorem finiteCoreCollarLift_radial_mfderiv (b : ι × Bool)
    (q : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv IR (𝓡 3) (radialCollarOrientationMap L (cuttingCollarWidth (precision b.1))) q =
      (mfderiv (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
        (finiteCoreCollarLift hL hδ f hf hdisj b q)).comp
      ((mfderiv IR (𝓡 3) (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)).comp
       (mfderiv IR IR (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) q)) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace E3 CoreCoordinateQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let N := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let κ := cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
  let jN := finiteCoreCollarLift hL hδ f hf hdisj b
  let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
  let ρ := radialCollarOrientationMap L (cuttingCollarWidth (precision b.1))
  have hj := (finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs).contMDiff
  have hκ := (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff
  have hjN := finiteCoreCollarLift_contMDiff I hdim hL hδ f hf hdisj hs b
  have hC := finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b
  have hN : (mfderiv IR (𝓡 3) jN q : ER →L[ℝ] E3) =
      mfderiv IR (𝓡 3) (j ∘ κ) q := (mfderiv_comp_open_val IR (𝓡 3) N jN hjN q).symm
  have hjκ : (mfderiv IR (𝓡 3) (j ∘ κ) q : ER →L[ℝ] E3) =
      (mfderiv IR (𝓡 3) j (κ q)).comp (mfderiv IR IR κ q) :=
    mfderiv_comp (f := κ) (g := j) q (hj.mdifferentiableAt (by simp)) (hκ.mdifferentiableAt (by simp))
  have hcomp : (mfderiv IR (𝓡 3) (C ∘ jN) q : ER →L[ℝ] E3) =
      (mfderiv (𝓡 3) (𝓡 3) C (jN q)).comp (mfderiv IR (𝓡 3) jN q) :=
    mfderiv_comp (f := jN) (g := C) q (hC.mdifferentiableAt (by simp)) (hjN.mdifferentiableAt (by simp))
  let D : (S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) → E3) → (ER →L[ℝ] E3) :=
    fun g => mfderiv IR (𝓡 3) g q
  have hd : (mfderiv IR (𝓡 3) (C ∘ jN) q : ER →L[ℝ] E3) = mfderiv IR (𝓡 3) ρ q :=
    congrArg D (finiteCoreCollarLift_radial_coordinate I hdim hL hδ f hf hdisj hs b)
  exact hd.symm.trans (hcomp.trans
    (congrArg (fun A : ER →L[ℝ] E3 => (mfderiv (𝓡 3) (𝓡 3) C (jN q)).comp A) (hN.trans hjκ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_mfderiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreCollarLift_radial_mfderiv
end DifferentialGeometry.Topology.ThreeManifold.Surgery
