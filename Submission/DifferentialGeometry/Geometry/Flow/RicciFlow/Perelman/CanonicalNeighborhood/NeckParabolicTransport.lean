import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessParabolicTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance neckParabolicC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckParabolicC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckParabolicC1 target :: scope.openDecls } }

private theorem parabolicTime_neckWindow_start (tau A s Q : ℝ)
    (hA : 0 < A) (hQ : 0 < Q) :
    parabolicTime tau A (s - (A⁻¹ * Q)⁻¹) = parabolicTime tau A s - Q⁻¹ := by
  dsimp only [parabolicTime]
  field_simp [hA.ne', hQ.ne']
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.parabolicTime_neckWindow_start
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.parabolicTime_neckWindow_start target :: scope.openDecls } }

def StrongNeck.parabolic {eps : ℝ} {x : M}
    (tau A : ℝ) (hA : 0 < A) (htau : tau ∈ D.carrier) (s : ℝ)
    (nk : StrongNeck S eps x (parabolicTime tau A s)) :
    StrongNeck (parabolicSolution S tau A hA htau) eps x s := by
  have hscalar : 0 < (parabolicSolution S tau A hA htau).scalar s x := by
    rw [parabolicSolution_scalar]
    exact mul_pos (inv_pos.mpr hA) nk.Q_pos
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hscalar
    cylinder := nk.cylinder
    map := nk.map
    center := nk.center
    center_eq := nk.center_eq
    domain := nk.domain
    time_domain := ?_
    comparison := ?_ }
  · intro r hr
    apply nk.time_domain
    have hmono : Monotone (parabolicTime tau A) := fun a b hab =>
      add_le_add_right (div_le_div_of_nonneg_right hab hA.le) tau
    have hstart := parabolicTime_neckWindow_start tau A s
      (S.scalar (parabolicTime tau A s) x) hA nk.Q_pos
    rw [parabolicSolution_scalar] at hr
    exact ⟨hstart ▸ hmono hr.1, hmono hr.2⟩
  · have hmetric : rescaledMetric (parabolicSolution S tau A hA htau) s
        ((parabolicSolution S tau A hA htau).scalar s x) hscalar =
        rescaledMetric S (parabolicTime tau A s)
          (S.scalar (parabolicTime tau A s) x) nk.Q_pos := by
      calc
        _ = rescaledMetric (parabolicSolution S tau A hA htau) s
            (A⁻¹ * S.scalar (parabolicTime tau A s) x)
            (mul_pos (inv_pos.mpr hA) nk.Q_pos) := by
          congr 1
          exact congrFun (congrFun (parabolicSolution_scalar S tau A hA htau) s) x
        _ = _ := rescaledMetric_paraSolution S tau A hA htau s
          (S.scalar (parabolicTime tau A s) x) nk.Q_pos
    rw [hmetric]
    exact nk.comparison

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic

def StrongNeck.ofParabolic {eps : ℝ} {x : M}
    (tau A : ℝ) (hA : 0 < A) (htau : tau ∈ D.carrier) (s : ℝ)
    (nk : StrongNeck (parabolicSolution S tau A hA htau) eps x s) :
    StrongNeck S eps x (parabolicTime tau A s) := by
  have hscalar : 0 < S.scalar (parabolicTime tau A s) x := by
    have h := nk.Q_pos
    rw [parabolicSolution_scalar] at h
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hA)).mp h
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hscalar
    cylinder := nk.cylinder
    map := nk.map
    center := nk.center
    center_eq := nk.center_eq
    domain := nk.domain
    time_domain := ?_
    comparison := ?_ }
  · intro r hr
    have hmono : Monotone (parabolicBackward tau A) := fun a b hab =>
      mul_le_mul_of_nonneg_left (sub_le_sub_right hab tau) hA.le
    have hstart := parabolicTime_neckWindow_start tau A s
      (S.scalar (parabolicTime tau A s) x) hA hscalar
    have hleft : parabolicBackward tau A
        (parabolicTime tau A s - (S.scalar (parabolicTime tau A s) x)⁻¹) =
        s - (A⁻¹ * S.scalar (parabolicTime tau A s) x)⁻¹ := by
      rw [← hstart, parabolicBackward_time hA.ne']
    have hright : parabolicBackward tau A (parabolicTime tau A s) = s :=
      parabolicBackward_time hA.ne'
    have hmem : parabolicBackward tau A r ∈ _root_.Set.Icc
        (s - ((parabolicSolution S tau A hA htau).scalar s x)⁻¹) s := by
      rw [parabolicSolution_scalar]
      exact ⟨hleft ▸ hmono hr.1, hright ▸ hmono hr.2⟩
    have hh := nk.time_domain hmem
    change parabolicTime tau A (parabolicBackward tau A r) ∈ D.carrier at hh
    simpa only [parabolicTime_back hA.ne'] using hh
  · have hmetric : rescaledMetric (parabolicSolution S tau A hA htau) s
        ((parabolicSolution S tau A hA htau).scalar s x) nk.Q_pos =
        rescaledMetric S (parabolicTime tau A s)
          (S.scalar (parabolicTime tau A s) x) hscalar := by
      calc
        _ = rescaledMetric (parabolicSolution S tau A hA htau) s
            (A⁻¹ * S.scalar (parabolicTime tau A s) x)
            (mul_pos (inv_pos.mpr hA) hscalar) := by
          congr 1
          exact congrFun (congrFun (parabolicSolution_scalar S tau A hA htau) s) x
        _ = _ := rescaledMetric_paraSolution S tau A hA htau s
          (S.scalar (parabolicTime tau A s) x) hscalar
    rw [← hmetric]
    exact nk.comparison

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic

@[simp] theorem StrongNeck.parabolic_map {eps : ℝ} {x : M}
    (tau A : ℝ) (hA : 0 < A) (htau : tau ∈ D.carrier) (s : ℝ)
    (nk : StrongNeck S eps x (parabolicTime tau A s)) :
    (nk.parabolic tau A hA htau s).map = nk.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.parabolic_map

@[simp] theorem StrongNeck.ofParabolic_map {eps : ℝ} {x : M}
    (tau A : ℝ) (hA : 0 < A) (htau : tau ∈ D.carrier) (s : ℝ)
    (nk : StrongNeck (parabolicSolution S tau A hA htau) eps x s) :
    (nk.ofParabolic tau A hA htau s).map = nk.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.ofParabolic_map

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
