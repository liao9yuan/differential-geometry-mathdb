import Submission.DifferentialGeometry.Topology.ThreeManifold.UncappingInteriorCover
import Submission.DifferentialGeometry.Topology.ThreeManifold.UncappingProjectionInterior
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private local instance smoothCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.smoothCellCharts
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.smoothCellCharts target :: scope.openDecls } }
private local instance smoothCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.smoothCellSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.smoothCellSmooth target :: scope.openDecls } }

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem exists_uncapping_homeomorph_localDiffeomorph :
    ∃ H : C.UncappingQuotient ≃ₜ M.Carrier,
      (∀ x : T.core, H (Quot.mk C.innerCapRelation
        (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
          (C.coreImageHomeomorph x))) = x.val) ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H) ∧
      ∀ (a : T.Index) (z : S2),
        IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ,ℝ)) (𝓡 3) ∞
          (H ∘ C.uncappingSeam a)
          (z,(⟨0,by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)) := by
  let v : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  obtain ⟨B,hsmall,hboundary,hhalf,hcollar,Ψ,ρ,hρ,hzero,hone,hpos,hgerm,_,hlo,hhi,H,hcore,hann⟩ :=
    C.exists_normalized_uncapping_homeomorph v
  obtain ⟨ε₀,ε₁,hε₀,hε₁,hloρ,hhiρ⟩ := hgerm
  have hmono : StrictMono (ρ : ℝ → ℝ) := strictMono_of_deriv_pos hpos
  have hρgerm : (ρ : ℝ → ℝ) =ᶠ[𝓝 (1 / 4 : ℝ)] (fun r => r - 1 / 4) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 4 : ℝ) hε₀] with r hr
    exact hloρ r (by
      have h : |r - 1 / 4| < ε₀ := by simpa only [_root_.Metric.mem_ball,Real.dist_eq] using hr
      exact h.le)
  refine ⟨H,hcore,?_,?_⟩
  · intro y
    let _ := C.coreCharts
    let _ := C.coreSmooth
    rcases C.uncappingInterior_cover B hsmall hboundary v y with ⟨x,hx,hy⟩ | ⟨b,z,hy⟩ | ⟨b,q,hq,hy⟩
    · have heq : y = ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ := Subtype.ext hy
      rw [heq]
      exact C.isLocalDiffeomorphAt_uncappingInteriorMap_core H hcore x hx
    · obtain ⟨e,⟨he,heq⟩,V,hV,hSV,hcap,_,_⟩ := hcollar b
      exact C.isLocalDiffeomorphAt_uncappingInteriorMap_outer H hcore
        (fun b => (B b).toHomeomorph) hsmall hboundary Ψ hlo hhi ρ hρ hann ε₁ hε₁ hhiρ b v e he heq V hV hSV
        (fun x hx => (hcap x hx).2) z y hy
    · have heq : y = ⟨C.capAnnulusInteriorChart b (B b) v q,
          C.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall b (B b) (hsmall b) v q hq⟩ :=
        Subtype.ext hy
      rw [heq]
      exact C.isLocalDiffeomorphAt_uncappingInteriorMap_annulus H B hsmall hboundary Ψ ρ hρ
        hmono hzero hone hann b v q hq
  · intro a z
    exact C.isLocalDiffeomorphAt_homeomorph_uncappingSeam H (fun b => (B b).toHomeomorph)
      hsmall hboundary hhalf Ψ ρ hρ hmono hzero hone hann hρgerm a z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.exists_uncapping_homeomorph_localDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.exists_uncapping_homeomorph_localDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.exists_uncapping_homeomorph_localDiffeomorph ``Submission.DifferentialGeometry.Topology.SphericalCapping.exists_uncapping_homeomorph_localDiffeomorph

theorem exists_core_neighborhood_partialDiffeomorph
    (x₀ : T.core) :
    ∃ F : PartialDiffeomorph (𝓡 3) (𝓡 3) M.Carrier N.Carrier ∞,
      T.core ⊆ F.source ∧ _root_.Set.range C.coreInclusion ⊆ F.target ∧
      (∀ x : T.core, F x.val = C.coreInclusion x) ∧
      ∀ x : T.core, F.symm (C.coreInclusion x) = x.val := by
  obtain ⟨H,hcore,hlocal,_⟩ := C.exists_uncapping_homeomorph_localDiffeomorph
  let f := C.uncappingInteriorMap H
  have hf : _root_.Function.Injective f := by
    intro x y h
    apply C.uncappingProjection_injective_on_interior
    exact H.injective h
  let hU : Nonempty C.uncappingInterior :=
    ⟨⟨C.coreInclusion x₀,C.coreInclusion_mem_uncappingInterior x₀⟩⟩
  obtain ⟨A,hAs,hAt,hAf⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      (hlocal.isLocalDiffeomorphOn _root_.Set.univ) isOpen_univ
      ⟨Classical.choice hU,_root_.Set.mem_univ _⟩ hf.injOn
  let B := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3)
    C.uncappingInterior hU
  let F := A.symm.trans B
  have hA (x : C.uncappingInterior) : A x = f x := congrFun hAf x
  have heq (x : T.core) : f ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ = x.val :=
    C.uncappingInteriorMap_core H hcore x
  have hAeq (x : T.core) : A ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ = x.val :=
    (hA _).trans (heq x)
  have hAtx (x : T.core) : x.val ∈ A.target := by
    rw [hAt]
    exact ⟨⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩,_root_.Set.mem_univ _,heq x⟩
  have hAi (x : T.core) : A.symm x.val = ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ := by
    rw [← hAeq x]
    exact A.left_inv (by rw [hAs]; exact _root_.Set.mem_univ _)
  have hsrc : T.core ⊆ F.source := by
    intro x hx
    exact ⟨hAtx ⟨x,hx⟩,_root_.Set.mem_univ _⟩
  have hFx (x : T.core) : F x.val = C.coreInclusion x := by
    change (A.symm x.val).val = _
    rw [hAi]
  refine ⟨F,hsrc,?_,hFx,?_⟩
  · rintro _ ⟨x,rfl⟩
    rw [← hFx x]
    exact F.map_source (hsrc x.property)
  · intro x
    rw [← hFx x]
    exact F.left_inv (hsrc x.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.exists_core_neighborhood_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.exists_core_neighborhood_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.exists_core_neighborhood_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.SphericalCapping.exists_core_neighborhood_partialDiffeomorph

end DifferentialGeometry.Topology.SphericalCapping
