import Submission.DifferentialGeometry.Topology.Manifold.Orientation
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {ι ι' ι'' : Type*}

private theorem orientation_reindex_trans (e : ι ≃ ι') (e' : ι' ≃ ι'')
    (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ E e' (Orientation.reindex ℝ E e o) =
      Orientation.reindex ℝ E (e.trans e') o := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.orientation_reindex_trans
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.orientation_reindex_trans target :: scope.openDecls } }

private theorem orientation_map_reindex (e : ι ≃ ι') (L : E ≃ₗ[ℝ] F)
    (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ F e (Orientation.map ι L o) =
      Orientation.map ι' L (Orientation.reindex ℝ E e o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.orientation_map_reindex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.orientation_map_reindex target :: scope.openDecls } }

variable {n : ℕ}

theorem tangentOrientationEquiv_reindex_eq_iff (L : E ≃ₗ[ℝ] F)
    (hE : Module.finrank ℝ E = n) (hF : Module.finrank ℝ F = n)
    (oE : Orientation ℝ E (Fin n)) (oF : Orientation ℝ F (Fin n)) :
    tangentOrientationEquiv L (Orientation.reindex ℝ E (finCongr hE.symm) oE) =
        Orientation.reindex ℝ F (finCongr hF.symm) oF ↔
      Orientation.map (Fin n) L oE = oF := by
  have hkey : (finCongr hE.symm).trans (finCongr L.finrank_eq) = finCongr hF.symm := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rfl
  have hmain : tangentOrientationEquiv L (Orientation.reindex ℝ E (finCongr hE.symm) oE) =
      Orientation.reindex ℝ F (finCongr hF.symm) (Orientation.map (Fin n) L oE) := by
    rw [tangentOrientationEquiv, Equiv.trans_apply]
    rw [(orientation_map_reindex (finCongr hE.symm) L oE).symm]
    rw [orientation_reindex_trans, hkey]
  rw [hmain]
  exact (Orientation.reindex ℝ F (finCongr hF.symm)).injective.eq_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_reindex_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_reindex_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_reindex_eq_iff ``Submission.DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_reindex_eq_iff

theorem tangentOrientationEquiv_symm_reindex_map (L : E ≃ₗ[ℝ] F)
    (hE : Module.finrank ℝ E = n) (hF : Module.finrank ℝ F = n)
    (oF : Orientation ℝ F (Fin n)) :
    Orientation.map (Fin n) L
      (Orientation.reindex ℝ E (finCongr hE)
        (tangentOrientationEquiv L.symm
          (Orientation.reindex ℝ F (finCongr hF.symm) oF))) = oF := by
  have hcomp : (finCongr hE).trans (finCongr hE.symm) =
      Equiv.refl (Fin (Module.finrank ℝ E)) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rfl
  have hinv : tangentOrientationEquiv L
      (tangentOrientationEquiv L.symm
        (Orientation.reindex ℝ F (finCongr hF.symm) oF)) =
      Orientation.reindex ℝ F (finCongr hF.symm) oF := by
    have h := tangentOrientationEquiv_symm L.symm
      (Orientation.reindex ℝ F (finCongr hF.symm) oF)
    simpa only [LinearEquiv.symm_symm] using h
  have hfix : Orientation.reindex ℝ E (finCongr hE.symm)
      (Orientation.reindex ℝ E (finCongr hE)
        (tangentOrientationEquiv L.symm
          (Orientation.reindex ℝ F (finCongr hF.symm) oF))) =
      tangentOrientationEquiv L.symm
        (Orientation.reindex ℝ F (finCongr hF.symm) oF) := by
    rw [orientation_reindex_trans, hcomp, Orientation.reindex_refl]
    rfl
  refine (tangentOrientationEquiv_reindex_eq_iff L hE hF
    (Orientation.reindex ℝ E (finCongr hE)
      (tangentOrientationEquiv L.symm
        (Orientation.reindex ℝ F (finCongr hF.symm) oF))) oF).mp ?_
  rw [hfix]
  exact hinv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_symm_reindex_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_symm_reindex_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_symm_reindex_map ``Submission.DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_symm_reindex_map

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H K M N : Type*}
variable [TopologicalSpace H] [TopologicalSpace K]
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
variable {n : ℕ}

omit [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
set_option backward.isDefEq.respectTransparency false in
theorem Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm
    (f : M ≃ₘ⟮I, J⟯ N)
    (hbij : ∀ x : M, Function.Bijective (mfderiv I J (f : M → N) x)) (x : M)
    (Y : Orientation ℝ F (Fin (Module.finrank ℝ F))) :
    tangentOrientationEquiv
        (differentialEquivOfBijective I J (f : M → N) hbij x).symm.toLinearEquiv Y =
      tangentOrientationEquiv
        (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.symm Y := rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.Manifold.Diffeomorph
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm ``Submission.DifferentialGeometry.Topology.Manifold.Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm

theorem Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv
    (f : M ≃ₘ⟮I, J⟯ N)
    (hbij : ∀ x : M, Function.Bijective (mfderiv I J (f : M → N) x))
    (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation J N n)
    (h : ∀ x : M, oM.orientation x = Orientation.reindex ℝ E (finCongr oM.dimension_eq)
      (tangentOrientationEquiv
        (differentialEquivOfBijective I J (f : M → N) hbij x).symm.toLinearEquiv
        (Orientation.reindex ℝ F (finCongr oN.dimension_eq.symm) (oN.orientation (f x))))) :
    f.preservesOrientation oM oN := by
  intro x
  have hbridge := Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm
    f hbij x
    (Orientation.reindex ℝ F (finCongr oN.dimension_eq.symm) (oN.orientation (f x)))
  rw [h x, hbridge]
  exact tangentOrientationEquiv_symm_reindex_map
    (E := TangentSpace I x) (F := TangentSpace J (f x))
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    oM.dimension_eq oN.dimension_eq (oN.orientation (f x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv ``Submission.DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv

theorem Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation
    (f : M ≃ₘ⟮I, J⟯ N) (hf : ContMDiff I J ∞ (f : M → N))
    (hbij : ∀ x : M, Function.Bijective (mfderiv I J (f : M → N) x))
    (o : SmoothOrientation J N) (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation J N n)
    (hN : ∀ y : N, o.val y =
      Orientation.reindex ℝ F (finCongr oN.dimension_eq.symm) (oN.orientation y))
    (hM : ∀ x : M, oM.orientation x = Orientation.reindex ℝ E (finCongr oM.dimension_eq)
      ((pullbackSmoothOrientation I J (f : M → N) hf hbij o).val x)) :
    f.preservesOrientation oM oN := by
  refine Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv
    f hbij oM oN fun x => ?_
  rw [hM x, pullbackSmoothOrientation_apply, hN (f x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem orientation_map_reindex_of_tangentOrientationEquiv
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {n : ℕ} (L : E ≃ₗ[ℝ] F) (hE : Module.finrank ℝ E = n) (hF : Module.finrank ℝ F = n)
    (oE : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (oF : Orientation ℝ F (Fin (Module.finrank ℝ F)))
    (h : tangentOrientationEquiv L oE = oF) :
    Orientation.map (Fin n) L (Orientation.reindex ℝ E (finCongr hE) oE) =
      Orientation.reindex ℝ F (finCongr hF) oF := by
  rw [← h]
  induction oE using Module.Ray.ind with
  | h vol hvol => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.orientation_map_reindex_of_tangentOrientationEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.orientation_map_reindex_of_tangentOrientationEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.orientation_map_reindex_of_tangentOrientationEquiv ``Submission.DifferentialGeometry.Topology.Manifold.orientation_map_reindex_of_tangentOrientationEquiv

end DifferentialGeometry.Topology.Manifold
