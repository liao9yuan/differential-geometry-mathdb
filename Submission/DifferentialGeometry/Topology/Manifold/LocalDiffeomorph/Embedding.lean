import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Function _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def neckExtendedChartDiffeomorph (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neckExtendedChartDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neckExtendedChartDiffeomorph target :: scope.openDecls } }

private def neckBoundarylessModelInverse : PartialDiffeomorph 𝓘(ℝ, E) I E H ∞ where
  toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(ℝ, E) I ∞ I.symm _root_.Set.univ
    simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := ∞)
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neckBoundarylessModelInverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neckBoundarylessModelInverse target :: scope.openDecls } }

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem localDiffeomorphAt_isImmersionAtOfComplement {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    IsImmersionAtOfComplement PUnit.{1} I J ∞ f x := by
  classical
  let L : E ≃L[ℝ] F := hf.mfderivToContinuousLinearEquiv (by decide)
  obtain ⟨φ, hxφ, hφ⟩ := hf
  let α : OpenPartialHomeomorph M H := (chartAt H x).restr φ.source
  let β := neckExtendedChartDiffeomorph (I := I) x
  let ψD := ((φ.symm.trans β).trans L.toDiffeomorph.toPartialDiffeomorph).trans
    (neckBoundarylessModelInverse (I := J))
  let ψ : OpenPartialHomeomorph N G := ψD.toOpenPartialHomeomorph
  have hαsource : α.source = (chartAt H x).source ∩ φ.source :=
    (chartAt H x).restr_source' φ.source φ.open_source
  have hxα : x ∈ α.source := by
    rw [hαsource]
    exact ⟨mem_chart_source H x, hxφ⟩
  have hαmax : α ∈ IsManifold.maximalAtlas I ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ I)
      (IsManifold.chart_mem_maximalAtlas x) φ.open_source
  have hψmax : ψ ∈ IsManifold.maximalAtlas J ∞ N :=
    ψ.mem_maximalAtlas_of_contMDiffOn ψD.contMDiffOn_toFun ψD.contMDiffOn_invFun
  have hψsource (y : M) (hy : y ∈ α.source) : f y ∈ ψ.source := by
    rw [hαsource] at hy
    change ((f y ∈ φ.target ∧ φ.symm (f y) ∈ (extChartAt I x).source) ∧ True) ∧ True
    refine ⟨⟨⟨?_, ?_⟩, trivial⟩, trivial⟩
    · rw [hφ hy.2]
      exact φ.map_source hy.2
    · have hleft : φ.symm.toPartialEquiv (φ.toPartialEquiv y) = y :=
        φ.toPartialEquiv.left_inv hy.2
      rw [hφ hy.2, hleft]
      simpa only [extChartAt_source] using hy.1
  have hψformula (y : M) (hy : y ∈ α.source) :
      (ψ.extend J) (f y) = L ((α.extend I) y) := by
    have hyφ : y ∈ φ.source := (hαsource ▸ hy).2
    have hleft : φ.symm.toPartialEquiv (φ.toPartialEquiv y) = y :=
      φ.toPartialEquiv.left_inv hyφ
    change J (J.symm (L ((extChartAt I x) (φ.symm (f y))))) = L ((α.extend I) y)
    rw [J.right_inv (by rw [J.range_eq_univ]; trivial), hφ hyφ,
      hleft]
    rfl
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ E PUnit.{1}).trans L) α ψ
    hxα (hψsource x hxα) hαmax hψmax hψsource ?_
  intro u hu
  let y := (α.extend I).symm u
  have hy : y ∈ α.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (α.extend I).map_target hu
  change (ψ.extend J) (f y) = L u
  rw [hψformula y hy]
  exact congrArg L ((α.extend I).right_inv hu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorphAt_isImmersionAtOfComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorphAt_isImmersionAtOfComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorphAt_isImmersionAtOfComplement ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorphAt_isImmersionAtOfComplement

theorem localDiffeomorph_isSmoothEmbedding_of_injective {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f) :
    IsSmoothEmbedding I J ∞ f := by
  have himm : _root_.Manifold.IsImmersionOfComplement PUnit.{1} I J ∞ f :=
    fun x => localDiffeomorphAt_isImmersionAtOfComplement (hf x)
  exact ⟨himm.isImmersion,
    (hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj).isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective

theorem diffeomorph_isSmoothEmbedding (f : M ≃ₘ⟮I, J⟯ N) :
    IsSmoothEmbedding I J ∞ f :=
  localDiffeomorph_isSmoothEmbedding_of_injective f.isLocalDiffeomorph f.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
