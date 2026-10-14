import Submission.DifferentialGeometry.Topology.ThreeManifold.CapComponentDiffeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallFinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_diffeomorph_finiteConnectedSum_capComponents :
    ∃ (W : Type u) (_ : Finite W)
      (assign : ConnectedComponents E.capped.Carrier → W)
      (L : W → List (ConnectedComponents E.capped.Carrier)) (k : W → ℕ),
      (∀ w K, K ∈ L w ↔ assign K = w) ∧ (∀ w, (L w).Nodup) ∧ (∀ w, L w ≠ []) ∧
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M.Carrier
        (Σ w, (finiteConnectedSum ((L w).map E.capped.component ++
          List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier) ∞) := by
  classical
  let N := E.capped.component
  let ep := E.cutCapVertex
  let ch := fun a t => E.capComponentBallChart (a,t)
  let hd := E.pairwise_disjoint_capComponentBallChart_image
  let := E.capped.finite_components
  choose C _ using fun K => PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N ep ch hd K
  obtain ⟨W,hW,assign,L,k,hm,hn,hne,Qcharts,hman,hcore,hseam,⟨D⟩⟩ :=
    PairedBallGluing.exists_finite_connectedSum_diffeomorph N ep ch hd C
  let _ := Qcharts
  obtain ⟨U⟩ := E.exists_pairedBallQuotient_diffeomorph C Qcharts hcore
    (fun a z => hseam a ⟨(z,0),Set.mem_univ _,by
      norm_num [SelfAttachment.directSeamDomain]⟩)
  exact ⟨W,hW,assign,L,k,hm,hn,hne,⟨U.symm.trans D⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_diffeomorph_finiteConnectedSum_capComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_diffeomorph_finiteConnectedSum_capComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_diffeomorph_finiteConnectedSum_capComponents ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_diffeomorph_finiteConnectedSum_capComponents

end DifferentialGeometry.Topology.SphericalCutCapTransition
