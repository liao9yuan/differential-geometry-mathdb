import Submission.DifferentialGeometry.Topology.Manifold.Sigma
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import Submission.DifferentialGeometry.Topology.Homeomorph.Sigma

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

theorem isLocalDiffeomorph_sum_inl : IsLocalDiffeomorph I I ∞ (Sum.inl : M → M ⊕ N) := by
  intro x
  let c := chartAt H x
  let d := c.lift_openEmbedding (_root_.Topology.IsOpenEmbedding.inl (X := M) (Y := N))
  let e := c.trans d.symm
  have hc : ContMDiffOn I I ∞ c c.source := contMDiffOn_chart
  have hc' : ContMDiffOn I I ∞ c.symm c.target := contMDiffOn_chart_symm
  have heqd : d = chartAt H (Sum.inl x : M ⊕ N) :=
    (ChartedSpace.sum_chartAt_inl x).symm
  have hd : ContMDiffOn I I ∞ d d.source := by
    rw [heqd]
    exact contMDiffOn_chart
  have hd' : ContMDiffOn I I ∞ d.symm d.target := by
    rw [heqd]
    exact contMDiffOn_chart_symm
  let D : PartialDiffeomorph I I M (M ⊕ N) ∞ :=
    { e with contMDiffOn_toFun := hd'.comp' hc, contMDiffOn_invFun := hc'.comp' hd }
  refine ⟨D, ⟨mem_chart_source H x, c.map_source (mem_chart_source H x)⟩, ?_⟩
  intro y hy
  change Sum.inl y = Sum.inl (c.symm (c y))
  rw [c.left_inv hy.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inl ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inl

theorem isLocalDiffeomorph_sum_inr : IsLocalDiffeomorph I I ∞ (Sum.inr : M → N ⊕ M) := by
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (Diffeomorph.sumComm I M ∞ N).isLocalDiffeomorph
    (isLocalDiffeomorph_sum_inl (I := I) (M := M) (N := N))
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inr ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_sum_inr

universe u v w
variable {ι : Type v} {X : ι → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)] [∀ i, IsManifold I ∞ (X i)]
  {F K P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [TopologicalSpace P] [ChartedSpace K P]

theorem isLocalDiffeomorph_sigma_iff (f : (Σ i, X i) → P) :
    IsLocalDiffeomorph I J ∞ f ↔ ∀ i, IsLocalDiffeomorph I J ∞ (f ∘ Sigma.mk i) := by
  constructor
  · intro hf i
    exact DifferentialGeometry.isLocalDiffeomorph_comp hf (isLocalDiffeomorph_sigmaMk i)
  · rintro hf ⟨i, x⟩
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hf i x) (isLocalDiffeomorph_sigmaMk i x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorph_sigma_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorph_sigma_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorph_sigma_iff ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_sigma_iff

variable {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace H (Y i)]
  [∀ i, IsManifold I ∞ (Y i)]

def sigmaCongrRightDiffeomorph (D : ∀ i, Diffeomorph I I (X i) (Y i) ∞) :
    Diffeomorph I I (Σ i, X i) (Σ i, Y i) ∞ := by
  let f : (Σ i, X i) → Σ i, Y i := fun x => ⟨x.fst, D x.fst x.snd⟩
  have hf : IsLocalDiffeomorph I I ∞ f := by
    apply (isLocalDiffeomorph_sigma_iff f).mpr
    intro i
    change IsLocalDiffeomorph I I ∞ (Sigma.mk i ∘ D i)
    exact DifferentialGeometry.isLocalDiffeomorph_comp (isLocalDiffeomorph_sigmaMk (M := Y) i) (D i).isLocalDiffeomorph
  exact hf.diffeomorphOfBijective (Equiv.sigmaCongrRight fun i => (D i).toEquiv).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph ``Submission.DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph

@[simp] theorem sigmaCongrRightDiffeomorph_apply
    (D : ∀ i, Diffeomorph I I (X i) (Y i) ∞) (i : ι) (x : X i) :
    sigmaCongrRightDiffeomorph D ⟨i, x⟩ = ⟨i, D i x⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.sigmaCongrRightDiffeomorph_apply

variable {V : Type v} (Z : Option V → Type u)
  [∀ i, TopologicalSpace (Z i)] [∀ i, ChartedSpace H (Z i)] [∀ i, IsManifold I ∞ (Z i)]

def sigmaOptionDiffeomorph : Diffeomorph I I (Σ i, Z i) (Z _root_.Option.none ⊕ (Σ i, Z (_root_.Option.some i))) ∞ := by
  have hf : IsLocalDiffeomorph I I ∞ (Homeomorph.sigmaOption Z) := by
    apply (isLocalDiffeomorph_sigma_iff _).mpr
    intro i
    cases i with
    | none => exact isLocalDiffeomorph_sum_inl (M := Z _root_.Option.none) (N := Σ i, Z (_root_.Option.some i))
    | some v =>
      change IsLocalDiffeomorph I I ∞ (Sum.inr ∘ (fun x : Z (_root_.Option.some v) => (⟨v, x⟩ : Σ j, Z (_root_.Option.some j))))
      exact DifferentialGeometry.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_sum_inr (I := I) (M := Σ j, Z (_root_.Option.some j)) (N := Z _root_.Option.none))
        (isLocalDiffeomorph_sigmaMk (I := I) (M := fun j => Z (_root_.Option.some j)) v)
  exact hf.diffeomorphOfBijective (Homeomorph.sigmaOption Z).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaOptionDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaOptionDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaOptionDiffeomorph ``Submission.DifferentialGeometry.Topology.sigmaOptionDiffeomorph

@[simp] theorem sigmaOptionDiffeomorph_apply (x : Σ i, Z i) :
    sigmaOptionDiffeomorph (I := I) Z x = Homeomorph.sigmaOption Z x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaOptionDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaOptionDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaOptionDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.sigmaOptionDiffeomorph_apply

end DifferentialGeometry.Topology
