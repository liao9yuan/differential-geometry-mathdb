import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBasis
import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.Topology.Homotopy.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Opposite

universe u

namespace DifferentialGeometry.Topology

private theorem dual_alternating_exactAt (A : ModuleCat.{u} ℤ) (n : ℕ) (hn : n ≠ 0) :
    ((((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (.up ℕ)).obj (ChainComplex.alternatingConst.obj A).op).ExactAt n := by
  let F := (_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  let K := (F.mapHomologicalComplex (.up ℕ)).obj (ChainComplex.alternatingConst.obj A).op
  change K.ExactAt n
  have hin : K.d (n - 1) n = if Even n then 𝟙 (F.obj (_root_.Opposite.op A)) else 0 := by
    change F.map ((if n - 1 + 1 = n then if Even n then 𝟙 A else 0 else 0).op) = _
    rw [if_pos (by omega)]
    split_ifs <;> simp
  have hout : K.d n (n + 1) = if Even (n + 1) then 𝟙 (F.obj (_root_.Opposite.op A)) else 0 := by
    change F.map ((if n + 1 = n + 1 then if Even (n + 1) then 𝟙 A else 0 else 0).op) = _
    rw [if_pos rfl]
    split_ifs <;> simp
  rw [HomologicalComplex.exactAt_iff' K (n - 1) n (n + 1)
    ((ComplexShape.up ℕ).prev_eq' (by change n - 1 + 1 = n; omega))
    ((ComplexShape.up ℕ).next_eq' rfl), ShortComplex.moduleCat_exact_iff]
  intro x hx
  by_cases he : Even n
  · refine ⟨x, ?_⟩
    change K.d (n - 1) n x = x
    rw [hin, if_pos he]
    rfl
  · change K.d n (n + 1) x = 0 at hx
    rw [hout, if_pos (Nat.even_add_one.mpr he)] at hx
    change x = 0 at hx
    refine ⟨0, ?_⟩
    change K.d (n - 1) n 0 = x
    rw [map_zero]
    exact hx.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.dual_alternating_exactAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.dual_alternating_exactAt target :: scope.openDecls } }

theorem integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace
    (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X]
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (integralSingularCohomology n X) := by
  let F := (_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  let e := _root_.AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    (ModuleCat.{u} ℤ) integralSingularCoefficients (TopCat.of X)
  let e' := (F.mapHomologicalComplex (.up ℕ)).mapIso
    ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).mapIso e.op) ≪≫
      integralSingularCochainsDualIso X
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact ((dual_alternating_exactAt _ n hn).of_iso e').isZero_homology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace ``Submission.DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace

theorem integralSingularCohomology_subsingleton_of_contractibleSpace
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (integralSingularCohomology n X) := by
  obtain ⟨p, hp⟩ := id_nullhomotopic X
  let Y := PUnit.{u + 1}
  let _ : Subsingleton (integralSingularCohomology n Y) :=
    integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace Y n hn
  let f : ContinuousMap X Y := ContinuousMap.const X PUnit.unit
  let g : ContinuousMap Y X := ContinuousMap.const Y p
  have hcomp : g.comp f = ContinuousMap.const X p := rfl
  have he := integralSingularCohomologyMap_eq_of_homotopic hp n
  rw [integralSingularCohomologyMap_id] at he
  have hc := integralSingularCohomologyMap_comp n f g
  rw [hcomp, ← he] at hc
  have hz (α : integralSingularCohomology n X) : α = 0 := by
    have ha := LinearMap.congr_fun hc α
    change α = integralSingularCohomologyMap n f (integralSingularCohomologyMap n g α) at ha
    rw [Subsingleton.elim (integralSingularCohomologyMap n g α) 0, map_zero] at ha
    exact ha
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_contractibleSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_contractibleSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_contractibleSpace ``Submission.DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_contractibleSpace

theorem integralSingularCohomology_subsingleton_of_isEmpty
    (X : Type u) [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    Subsingleton (integralSingularCohomology n X) := by
  have hs : Subsingleton (integralSingularCochain n X) := by
    refine ⟨fun φ ψ => (integralSingularChainBasis n X).ext fun σ => ?_⟩
    exact isEmptyElim (integralSingularSimplexEquiv n X σ
      ⟨Pi.single (0 : Fin (n + 1)) 1, single_mem_stdSimplex ℝ 0⟩)
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply HomologicalComplex.ExactAt.isZero_homology
  exact ((integralSingularCochains X).sc n).exact_of_isZero_X₂
    (ModuleCat.isZero_iff_subsingleton.mpr hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_isEmpty ``Submission.DifferentialGeometry.Topology.integralSingularCohomology_subsingleton_of_isEmpty

end DifferentialGeometry.Topology

end
