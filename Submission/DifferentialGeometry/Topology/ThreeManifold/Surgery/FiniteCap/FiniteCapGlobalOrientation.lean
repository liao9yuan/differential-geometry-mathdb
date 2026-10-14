import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapOverlapCoordinates
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingAnnulusOrientation
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen

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

private theorem cap_old_orientation_eq (b : ι × Bool) (o : SmoothOrientation I M)
    (oE : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)))
    (hAnn : ∀ x : cuttingAnnulus L (precision b.1),
      tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) I
        (f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2)
        (cuttingAnnulusAmbient_mfderiv_bijective I hδ f hs hL b) x).toLinearEquiv oE =
          o.val (f b.1 (cuttingAnnulusCylinderMap hL (hδ b.1) b.2 x)))
    (p : finiteCapOldOverlapOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    (finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b oE).val ⟨p.val, p.property.1⟩ =
      (finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val ⟨p.val, p.property.2⟩ := by
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let pC : finiteCapNeighborhoodOpens hL hδ f hf hdisj b := ⟨p.val, p.property.1⟩
  let pO : finiteCoreInteriorOpens hL hδ f hf hdisj := ⟨p.val, p.property.2⟩
  let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
  let σ := finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs
  let F := f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2
  let x := finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b p
  let eC : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡 3) (𝓡 3) C
    (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) pC
  let eO : E3 ≃L[ℝ] E := differentialEquivOfBijective (𝓡 3) I σ
    (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) pO
  let eF : E3 ≃L[ℝ] E := differentialEquivOfBijective (𝓡 3) I F
    (cuttingAnnulusAmbient_mfderiv_bijective I hδ f hs hL b) x
  have hD : eO = eC.trans eF := by
    apply ContinuousLinearEquiv.ext
    funext v
    have hO := congrArg (fun D : E3 →L[ℝ] E => D v)
      (finiteCapOldOverlap_old_mfderiv I hdim hL hδ f hf hdisj hs b p)
    have hC := congrArg (fun D : E3 →L[ℝ] E3 => D v)
      (finiteCapOldOverlap_radial_mfderiv I hdim hL hδ f hf hdisj hs b p)
    exact hO.trans (congrArg (mfderiv (𝓡 3) I F x) hC.symm)
  let OC := (finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b oE).val pC
  let OO := (finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val pO
  have hC : tangentOrientationEquiv eC.toLinearEquiv OC = oE :=
    finiteCapNeighborhoodSmoothOrientation_pushforward I hdim hL hδ f hf hdisj hs b oE pC
  have hO : tangentOrientationEquiv eO.toLinearEquiv OO = o.val (σ pO) :=
    finiteOldSmoothOrientation_pushforward I hdim hL hδ f hf hdisj hs o pO
  have hPoint : σ pO = F x :=
    congrFun (finiteCapOldOverlap_old_coordinate I hdim hL hδ f hf hdisj hs b) p
  apply (tangentOrientationEquiv eO.toLinearEquiv).injective
  calc
    tangentOrientationEquiv eO.toLinearEquiv OC =
        tangentOrientationEquiv eF.toLinearEquiv (tangentOrientationEquiv eC.toLinearEquiv OC) := by
          rw [hD]
          exact tangentOrientationEquiv_trans eC.toLinearEquiv eF.toLinearEquiv OC
    _ = tangentOrientationEquiv eF.toLinearEquiv oE := congrArg _ hC
    _ = o.val (F x) := hAnn x
    _ = o.val (σ pO) := congrArg o.val hPoint.symm
    _ = tangentOrientationEquiv eO.toLinearEquiv OO := hO.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cap_old_orientation_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.cap_old_orientation_eq target :: scope.openDecls } }

theorem exists_finiteCapSmoothOrientation (o : SmoothOrientation I M) :
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
        ∀ (b : ι × Bool) (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b),
          oQ.val p.val = (finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b (oE b)).val p := by
  classical
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  have hex : ∀ b : ι × Bool, ∃ oE : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      (oE = (Module.finBasis ℝ E3).orientation ∨ oE = -(Module.finBasis ℝ E3).orientation) ∧
      (letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
       letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
       ∀ q : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)),
         (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE).val q =
           (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q) ∧
      ∀ p : finiteCapOldOverlapOpens hL hδ f hf hdisj b,
        (finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b oE).val ⟨p.val, p.property.1⟩ =
          (finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val ⟨p.val, p.property.2⟩ := by
    intro b
    let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    obtain ⟨oE, hsign, hcollar, hAnn⟩ :=
      exists_radialOrientation_matching_collar_and_annulus I hdim hδ f hf hdisj hs hL b o
    exact ⟨oE, hsign, hcollar, fun p => cap_old_orientation_eq I hdim hL hδ f hf hdisj hs b o oE hAnn p⟩
  choose oE hsign hcollar hover using hex
  let U : Option (ι × Bool) → _root_.TopologicalSpace.Opens OrientedQ := fun i => match i with
    | none => finiteCoreInteriorOpens hL hδ f hf hdisj
    | some b => finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let O : ∀ i, SmoothOrientation (𝓡 3) (U i) := fun i => match i with
    | none => finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o
    | some b => finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b (oE b)
  have hcover : ∀ p : OrientedQ, ∃ i, p ∈ U i := by
    intro p
    rcases eq_univ_iff_forall.mp (finiteCapNeighborhood_cover hL hδ f hf hdisj) p with hp | hp
    · exact ⟨none, hp⟩
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hp
      exact ⟨some b, hb⟩
  have heq : ∀ (i j : Option (ι × Bool)) (p : OrientedQ) (hi : p ∈ U i) (hj : p ∈ U j),
      (O i).val ⟨p, hi⟩ = (O j).val ⟨p, hj⟩ := by
    intro i j p hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some b => exact (hover b ⟨p, hj, hi⟩).symm
    | some b =>
      cases j with
      | none => exact hover b ⟨p, hi, hj⟩
      | some c =>
        by_cases hbc : b = c
        · subst c
          rfl
        · exact False.elim (disjoint_left.mp
            (pairwise_disjoint_finiteCapNeighborhoods hL hδ f (fun i => (hf i).injective) hdisj hbc) hi hj)
  exact ⟨oE, glueSmoothOrientations (𝓡 3) U O hcover heq, hsign, hcollar,
    fun p => glueSmoothOrientations_apply (𝓡 3) U O hcover heq _root_.Option.none p,
    fun b p => glueSmoothOrientations_apply (𝓡 3) U O hcover heq (_root_.Option.some b) p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_finiteCapSmoothOrientation
end DifferentialGeometry.Topology.ThreeManifold.Surgery
