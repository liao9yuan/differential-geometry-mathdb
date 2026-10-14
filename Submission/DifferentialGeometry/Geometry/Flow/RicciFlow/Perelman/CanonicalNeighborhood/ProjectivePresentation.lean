import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunction
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import Mathlib.Topology.Homeomorph.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Topology _root_.Submission.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
  [IsManifold I3 ∞ Z]

private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

theorem ProjectivePresentation.isLocalDiffeomorph (pr : ProjectivePresentation Z) :
    IsLocalDiffeomorph (𝓡 3) I3 ∞ pr.quotient := by
  intro x
  apply DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    isOpen_univ (_root_.Set.mem_univ x) pr.smooth.contMDiffOn
  exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡 3) I3 pr.quotient x).toLinearMap
    (pr.local_diffeo x)).toContinuousLinearEquiv, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.isLocalDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.isLocalDiffeomorph

theorem ProjectivePresentation.exists_realProjectiveThree_diffeomorph
    (pr : ProjectivePresentation Z) :
    ∃ e : RealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ Z,
      ∀ a : Sphere 3, e (realProjectiveSpaceQuotientMap a) = pr.quotient a := by
  let f : C(Sphere 3, Z) := ⟨pr.quotient, pr.smooth.continuous⟩
  let q : C(Sphere 3, RealProjectiveThreeSpace) :=
    ⟨realProjectiveSpaceQuotientMap,
      (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (n := 3)).contMDiff.continuous⟩
  have hq : _root_.Topology.IsQuotientMap q := (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (n := 3)).isOpenMap.isQuotientMap
    q.continuous realProjectiveSpaceQuotientMap_surjective
  have hf : _root_.Topology.IsQuotientMap f := pr.isLocalDiffeomorph.isOpenMap.isQuotientMap f.continuous pr.onto
  have hker (x y : Sphere 3) : Setoid.ker q x y ↔ Setoid.ker f x y :=
    (realProjectiveSpaceQuotientMap_eq_iff (x := x) (y := y)).trans (pr.fibers x y).symm
  let e : Quotient (Setoid.ker q) ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  let d := (hq.homeomorph.symm.trans e).trans hf.homeomorph
  have hd (a : Sphere 3) : d (realProjectiveSpaceQuotientMap a) = pr.quotient a := by
    have ha : hq.homeomorph (Quotient.mk (Setoid.ker q) a) = q a := rfl
    change hf.homeomorph (e (hq.homeomorph.symm (q a))) = f a
    rw [← ha, hq.homeomorph.symm_apply_apply]
    rfl
  obtain ⟨D, hD⟩ := KappaSolutions.exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
    q (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (n := 3)) realProjectiveSpaceQuotientMap_surjective
    f pr.isLocalDiffeomorph d hd
  exact ⟨D, fun a => (congrFun hD (realProjectiveSpaceQuotientMap a)).trans (hd a)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.exists_realProjectiveThree_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.exists_realProjectiveThree_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.exists_realProjectiveThree_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation.exists_realProjectiveThree_diffeomorph

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
