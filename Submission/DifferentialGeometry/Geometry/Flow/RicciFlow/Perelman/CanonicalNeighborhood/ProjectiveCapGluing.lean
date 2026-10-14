import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplement
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.AffineThreeBall
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
open private capCore_of_puncturedProjectiveDiffeomorph from Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {P M : Type*} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]

theorem exists_projectivePresentation_of_diagonal_slab_and_exterior_ball
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ P)
    (Phi : PartialDiffeomorph I3 I3 P M ∞) {L : ℝ} (hL : 0 < L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ⊆ Phi.source)
    (G : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hG : Metric.closedBall (0 : ThreeSpace) 1 ⊆ G.source)
    (hGo : G '' Metric.ball (0 : ThreeSpace) 1 =
      (Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L))))ᶜ)
:
    ∃ e : RealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ M,
      (∀ z : Cylinder, z ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-L) L →
        e (Geometry.cylinderDiagonalQuotientDiffeomorph (Geometry.cylinderDiagonalQuotientMap z)).val =
          Phi (d (Geometry.cylinderDiagonalQuotientMap z))) ∧
      ∃ pr : ProjectivePresentation M,
        (∀ a : Sphere 3, pr.quotient a = e (realProjectiveSpaceQuotientMap a)) ∧
        ∃ D : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace,
          D '' Metric.closedBall (0 : ThreeSpace) 1 = Metric.closedBall (0 : ThreeSpace) 1 ∧
          (∀ z ∈ Metric.closedBall (0 : ThreeSpace) 1,
            e (realProjectiveThreeAffineBall L hL.ne' z) = G (D z)) := by
  let E := Geometry.cylinderDiagonalQuotientDiffeomorph
  let ep := E.symm.trans d
  let b := realProjectiveThreeAffineBall L hL.ne'
  have hb2 : Metric.closedBall (0 : ThreeSpace) 2 ⊆ b.source :=
    realProjectiveThreeAffineBall_contains_closedBall L hL.ne'
  have hb1 : Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
    (Metric.closedBall_subset_closedBall (by norm_num)).trans hb2
  obtain ⟨T, hTsource, hT, _hcore⟩ := capCore_of_puncturedProjectiveDiffeomorph ep b hb2
    (by rw [realProjectiveThreeAffineBall_apply, realProjectiveThreeAffineBallMap_zero])
  let K := (b '' Metric.ball (0 : ThreeSpace) 1)ᶜ
  have hKT : K ⊆ T.source := by
    intro y hy
    rw [hTsource]
    intro heq
    exact hy ⟨0, by simp, (by rw [realProjectiveThreeAffineBall_apply,
      realProjectiveThreeAffineBallMap_zero]; exact heq.symm)⟩
  have hTimage : T '' K = d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) := by
    rw [show K = (realProjectiveThreeAffineBall L hL.ne' '' Metric.ball (0 : ThreeSpace) 1)ᶜ from rfl,
      realProjectiveThreeAffineBall_complement_eq_slab_image hL, _root_.Set.image_image, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro z hz
    have hh := hT (E (Geometry.cylinderDiagonalQuotientMap z))
    have hproj : (E (Geometry.cylinderDiagonalQuotientMap z)).val =
        realProjectiveSpaceQuotientMap
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture z).val := rfl
    rw [hproj] at hh
    change T _ = d (E.symm (E (Geometry.cylinderDiagonalQuotientMap z))) at hh
    simpa only [Diffeomorph.symm_apply_apply] using hh
  let Q := T.trans Phi
  let U := Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)))
  have hKQ : K ⊆ Q.source := by
    intro y hy
    exact ⟨hKT hy, hsource (hTimage ▸ _root_.Set.mem_image_of_mem T hy)⟩
  have hQU : Q '' K = U := by
    change (Phi ∘ T) '' K = U
    rw [_root_.Set.image_comp, hTimage]
  obtain ⟨e, heQ, _heBall, D, hDball, heG, O, hOo, hKO, hOQ, heO⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball b Q G
      hb1 hKQ hG hQU hGo
  refine ⟨e, ?_, realProjectiveThreePresentation.map e, fun _ => rfl, D, hDball, heG⟩
  intro z hz
  have hproj : (E (Geometry.cylinderDiagonalQuotientMap z)).val ∈ K := by
    rw [show K = (realProjectiveThreeAffineBall L hL.ne' '' Metric.ball (0 : ThreeSpace) 1)ᶜ from rfl,
      realProjectiveThreeAffineBall_complement_eq_slab_image hL]
    exact ⟨z, hz, rfl⟩
  rw [heQ hproj]
  change Phi (T (E (Geometry.cylinderDiagonalQuotientMap z)).val) = _
  rw [hT]
  change Phi (d (E.symm (E (Geometry.cylinderDiagonalQuotientMap z)))) = _
  rw [Diffeomorph.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projectivePresentation_of_diagonal_slab_and_exterior_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projectivePresentation_of_diagonal_slab_and_exterior_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projectivePresentation_of_diagonal_slab_and_exterior_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projectivePresentation_of_diagonal_slab_and_exterior_ball

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
