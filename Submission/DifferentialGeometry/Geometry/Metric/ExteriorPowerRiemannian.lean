import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPowerBundle
import Submission.DifferentialGeometry.Bundle.Equiv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Algebra.Structures

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.BigOperators _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace _root_.Topology

namespace Bundle.Trivialization
open _root_.Bundle _root_.Bundle.Trivialization

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V]

open _root_.Bundle _root_.Bundle.Trivialization in
private theorem contMDiffAt_inner_map_exteriorPower_symmL (k : ℕ)
    (e : _root_.Bundle.Trivialization F (π F V)) [MemTrivializationAtlas e]
    {x : B} (hx : x ∈ e.baseSet) (u v : ⋀[ℝ]^k F) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    ContMDiffAt IB 𝓘(ℝ, ℝ) n
      (fun y => ⟪exteriorPower.map k (e.symmL ℝ y).toLinearMap u,
        exteriorPower.map k (e.symmL ℝ y).toLinearMap v⟫) x := by
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  classical
  have hsec (w : F) :
      ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n
        (fun y => (⟨y, e.symmL ℝ y w⟩ : _root_.Bundle.TotalSpace F V)) x := by
    have h := (e.contMDiffOn_symm (IB := IB) (n := n)).comp
      (contMDiffOn_id.prodMk (contMDiffOn_const (c := w)))
      (fun y hy => e.mem_target.mpr hy)
    apply (h.contMDiffAt (e.open_baseSet.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.symmL_apply hy, e.mk_symm hy]
    rfl
  have hgen (a b : Fin k → F) :
      ContMDiffAt IB 𝓘(ℝ, ℝ) n
        (fun y => ⟪exteriorPower.map k (e.symmL ℝ y).toLinearMap
          (exteriorPower.ιMulti ℝ k a),
          exteriorPower.map k (e.symmL ℝ y).toLinearMap
            (exteriorPower.ιMulti ℝ k b)⟫) x := by
    simp only [exteriorPower.map_apply_ιMulti, exteriorPower.inner_ιMulti_ιMulti,
      Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
    apply ContMDiffAt.sum
    intro σ _
    apply contMDiffAt_const.mul
    exact ContMDiffAt.prod fun i _ => (hsec (a i)).inner_bundle (hsec (b (σ i)))
  have hu : u ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ k (M := F))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  have hv : v ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ k (M := F))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      exact hgen a b
    | zero =>
      simp only [map_zero, inner_zero_right]
      exact contMDiffAt_const
    | add u v _ _ hu hv =>
      simp only [map_add, inner_add_right]
      exact hu.add hv
    | smul c u _ hu =>
      simp only [map_smul, real_inner_smul_right]
      exact contMDiffAt_const.mul hu
  | zero =>
    simp only [map_zero, inner_zero_left]
    exact contMDiffAt_const
  | add u v _ _ hu hv =>
    simp only [map_add, inner_add_left]
    exact hu.add hv
  | smul c u _ hu =>
    simp only [map_smul, real_inner_smul_left]
    exact contMDiffAt_const.mul hu

run_cmd do
  let target := ``Submission.Bundle.Trivialization.contMDiffAt_inner_map_exteriorPower_symmL
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.Trivialization.contMDiffAt_inner_map_exteriorPower_symmL target :: scope.openDecls } }

end Bundle.Trivialization

namespace Bundle.ExteriorPower
open _root_.Bundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V]

theorem isContMDiffRiemannianBundle (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    IsContMDiffRiemannianBundle IB n (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  refine ⟨fun x => innerSL ℝ, ?_, fun x v w => rfl⟩
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise
  intro u
  apply contMDiffAt_clm_of_pointwise
  intro v
  let e := _root_.FiberBundle.trivializationAt F V x
  have hx : x ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V x
  have h := Trivialization.contMDiffAt_inner_map_exteriorPower_symmL
    (IB := IB) (n := n) k e hx u v
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  have hey : y ∈ (_root_.FiberBundle.trivializationAt (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) x).baseSet := hy
  rw [inCoordinates_apply_eq₂ hey hey (by simp)]
  rw [Trivialization.coe_linearMapAt_of_mem (R := ℝ)
    (_root_.FiberBundle.trivializationAt ℝ (fun _ : B => ℝ) x) (by simp)]
  change ⟪(_root_.FiberBundle.trivializationAt (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) x).symm y u,
      (_root_.FiberBundle.trivializationAt (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) x).symm y v⟫ = _
  rw [trivializationAt_eq F V k x, trivialization_symm_apply F V k e hy,
    trivialization_symm_apply F V k e hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ExteriorPower.isContMDiffRiemannianBundle then
    throwError "Refusing to shadow existing declaration Bundle.ExteriorPower.isContMDiffRiemannianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ExteriorPower.isContMDiffRiemannianBundle ``Submission.Bundle.ExteriorPower.isContMDiffRiemannianBundle

end Bundle.ExteriorPower
