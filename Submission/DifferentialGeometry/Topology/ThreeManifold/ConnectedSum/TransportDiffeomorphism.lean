import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.LocalDiffeomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.ConnectedSumQuotient

namespace DifferentialGeometry.Topology

universe u v u' v'

private theorem isLocalDiffeomorphAt_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
    {f g : M → N} {x : M} (h : f =ᶠ[𝓝 x] g)
    (hg : IsLocalDiffeomorphAt I J n g x) : IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨φ, hx, hφ⟩ := hg
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp h
  have hsm : ∀ y ∈ φ.toPartialEquiv.source ∩ W, f y = φ.toPartialEquiv.toFun y :=
    fun y hy => (hWsub hy.2).trans (hφ hy.1)
  refine ⟨{ toFun := f
            invFun := φ.toPartialEquiv.invFun
            source := φ.toPartialEquiv.source ∩ W
            target := φ.toPartialEquiv.toFun '' (φ.toPartialEquiv.source ∩ W)
            map_source' := fun y hy => ⟨y, hy, (hsm y hy).symm⟩
            map_target' := fun y hy => by
              obtain ⟨z, hz, rfl⟩ := hy
              rw [φ.toPartialEquiv.left_inv' hz.1]
              exact hz
            left_inv' := fun y hy => by
              rw [hsm y hy]
              exact φ.toPartialEquiv.left_inv' hy.1
            right_inv' := fun y hy => by
              obtain ⟨z, hz, rfl⟩ := hy
              rw [φ.toPartialEquiv.left_inv' hz.1]
              exact hsm z hz
            open_source := φ.open_source.inter hWopen
            open_target := φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
              (φ.open_source.inter hWopen) _root_.Set.inter_subset_left
            contMDiffOn_toFun := (φ.contMDiffOn_toFun.mono _root_.Set.inter_subset_left).congr
              (fun y hy => hsm y hy)
            contMDiffOn_invFun := φ.contMDiffOn_invFun.mono
              (by rintro z ⟨w, hw, rfl⟩; exact φ.map_source hw.1) },
    ⟨hx, hxW⟩, fun y hy => rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_eventuallyEq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_eventuallyEq target :: scope.openDecls } }

section SubtypeMap

variable {M : Type u} [TopologicalSpace M] [ChartedSpace csModel M] [IsManifold (𝓡 3) ∞ M]
  {M' : Type u'} [TopologicalSpace M'] [ChartedSpace csModel M'] [IsManifold (𝓡 3) ∞ M']

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ M'] in
theorem isLocalDiffeomorph_subtypeMap
    (Φd : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M') (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens M') (hUV : ∀ x : U, Φd (x : M) ∈ V)
    (hVU : ∀ y : V, Φd.symm (y : M') ∈ U) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : U => (⟨Φd (x : M), hUV x⟩ : V)) := by
  let φ : PartialDiffeomorph (𝓡 3) (𝓡 3) U V ∞ :=
    { toFun := fun x : U => (⟨Φd (x : M), hUV x⟩ : V)
      invFun := fun y : V => (⟨Φd.symm (y : M'), hVU y⟩ : U)
      source := Set.univ
      target := Set.univ
      map_source' := fun x _ => Set.mem_univ _
      map_target' := fun y _ => Set.mem_univ _
      left_inv' := fun x _ => Subtype.ext (Φd.left_inv (x : M))
      right_inv' := fun y _ => Subtype.ext (Φd.right_inv (y : M'))
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun := by
        intro x _
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff (U := V)]
        exact Φd.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
          (contMDiff_subtype_val (U := U)).contMDiffAt.contMDiffWithinAt
      contMDiffOn_invFun := by
        intro y _
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff (U := U)]
        exact Φd.symm.contMDiff.contMDiffAt.comp_contMDiffWithinAt y
          (contMDiff_subtype_val (U := V)).contMDiffAt.contMDiffWithinAt }
  exact fun x => ⟨φ, Set.mem_univ x, fun y _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorph_subtypeMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorph_subtypeMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorph_subtypeMap ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_subtypeMap

end SubtypeMap

section Transport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace csModel M]
  {M' : Type u'} [TopologicalSpace M'] [ChartedSpace csModel M']
  {N : Type v} [TopologicalSpace N] [ChartedSpace csModel N]
  {N' : Type v'} [TopologicalSpace N'] [ChartedSpace csModel N']

variable (c : BallChart 3 (𝓡 3) M) (c' : BallChart 3 (𝓡 3) M')
variable (d : BallChart 3 (𝓡 3) N) (d' : BallChart 3 (𝓡 3) N')
variable (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
variable (Φ : M ≃ₜ M') (Ψ : N ≃ₜ N')
variable (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
variable (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)

omit [ChartedSpace csModel M] [ChartedSpace csModel M'] [ChartedSpace csModel N]
  [ChartedSpace csModel N'] in
theorem closedBall_two_subset_iff' {x : csModel} (hx : x ∈ Metric.closedBall (0 : csModel) 1) :
    x ∈ Metric.closedBall (0 : csModel) 2 :=
  Metric.closedBall_subset_closedBall (by norm_num) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedBall_two_subset_iff' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedBall_two_subset_iff'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedBall_two_subset_iff' ``Submission.DifferentialGeometry.Topology.closedBall_two_subset_iff'

theorem chart_image_ball_of_closedBall_two'
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x) :
    Φ '' (c.chart '' Metric.ball (0 : csModel) 1) = c'.chart '' Metric.ball (0 : csModel) 1 := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hΦ x (closedBall_two_subset_iff' (Metric.ball_subset_closedBall hx))).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c.chart x, ⟨x, hx, rfl⟩,
      hΦ x (closedBall_two_subset_iff' (Metric.ball_subset_closedBall hx))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.chart_image_ball_of_closedBall_two' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.chart_image_ball_of_closedBall_two'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.chart_image_ball_of_closedBall_two' ``Submission.DifferentialGeometry.Topology.chart_image_ball_of_closedBall_two'

theorem chart_sphere_agreement_of_closedBall_two'
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (z : csSphere) : Φ (c.chart (z : csModel)) = c'.chart (z : csModel) :=
  hΦ (z : csModel) (closedBall_two_subset_iff' (Metric.sphere_subset_closedBall z.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.chart_sphere_agreement_of_closedBall_two' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.chart_sphere_agreement_of_closedBall_two'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.chart_sphere_agreement_of_closedBall_two' ``Submission.DifferentialGeometry.Topology.chart_sphere_agreement_of_closedBall_two'

def csTransport
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x) :
    ConnectedSumQuotient c d aD.toHomeomorph ≃ₜ ConnectedSumQuotient c' d' aD.toHomeomorph :=
  homeomorphOfBallImage c c' d d' aD.toHomeomorph aD.toHomeomorph Φ Ψ
    (chart_image_ball_of_closedBall_two' c c' Φ hΦ)
    (chart_image_ball_of_closedBall_two' d d' Ψ hΨ)
    (Homeomorph.refl csSphere)
    (fun z => by simpa using chart_sphere_agreement_of_closedBall_two' c c' Φ hΦ z)
    (fun z => by simpa using chart_sphere_agreement_of_closedBall_two' d d' Ψ hΨ (aD z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csTransport ``Submission.DifferentialGeometry.Topology.csTransport

theorem puncturedHomeomorphOfImage_val (Φ : M ≃ₜ M')
    (h : Φ '' (c.chart '' Metric.ball (0 : csModel) 1) =
      c'.chart '' Metric.ball (0 : csModel) 1) (y : c.Punctured) :
    ((BallChart.puncturedHomeomorphOfImage c c' Φ h y : c'.Punctured) : M') = Φ y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.puncturedHomeomorphOfImage_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.puncturedHomeomorphOfImage_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.puncturedHomeomorphOfImage_val ``Submission.DifferentialGeometry.Topology.puncturedHomeomorphOfImage_val

theorem csTransport_inl
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)
    (y : c.Punctured) :
    csTransport c c' d d' aD Φ Ψ hΦ hΨ (inl c d aD.toHomeomorph y)
      = inl c' d' aD.toHomeomorph (BallChart.puncturedHomeomorphOfImage c c' Φ
          (chart_image_ball_of_closedBall_two' c c' Φ hΦ) y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csTransport_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csTransport_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csTransport_inl ``Submission.DifferentialGeometry.Topology.csTransport_inl

theorem csTransport_inr
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)
    (y : d.Punctured) :
    csTransport c c' d d' aD Φ Ψ hΦ hΨ (inr c d aD.toHomeomorph y)
      = inr c' d' aD.toHomeomorph (BallChart.puncturedHomeomorphOfImage d d' Ψ
          (chart_image_ball_of_closedBall_two' d d' Ψ hΨ) y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csTransport_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csTransport_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csTransport_inr ``Submission.DifferentialGeometry.Topology.csTransport_inr

end Transport

section Interior

variable {M : Type u} [TopologicalSpace M] [ChartedSpace csModel M]
  {M' : Type u'} [TopologicalSpace M'] [ChartedSpace csModel M']
  {N : Type v} [TopologicalSpace N] [ChartedSpace csModel N]
  {N' : Type v'} [TopologicalSpace N'] [ChartedSpace csModel N']

variable (c : BallChart 3 (𝓡 3) M) (c' : BallChart 3 (𝓡 3) M')
variable (d : BallChart 3 (𝓡 3) N) (d' : BallChart 3 (𝓡 3) N')
variable (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
variable (Φ : M ≃ₜ M') (Ψ : N ≃ₜ N')
variable (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
variable (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)

variable [T2Space M] [T2Space M'] [T2Space N] [T2Space N']

theorem map_mem_interior'
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (x : c.interior) : Φ (x : M) ∈ c'.interior := by
  rw [BallChart.mem_interior]
  rintro ⟨w, hw, hweq⟩
  have hw2 : w ∈ Metric.closedBall (0 : csModel) 2 := closedBall_two_subset_iff' hw
  have hxw : Φ (x : M) = Φ (c.chart w) := by
    rw [← hweq]
    exact (hΦ w hw2).symm
  exact x.2 ⟨w, hw, (Φ.injective hxw).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.map_mem_interior' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.map_mem_interior'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.map_mem_interior' ``Submission.DifferentialGeometry.Topology.map_mem_interior'

theorem symm_map_mem_interior'
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (y : c'.interior) : Φ.symm (y : M') ∈ c.interior := by
  rw [BallChart.mem_interior]
  rintro ⟨w, hw, hweq⟩
  have hw2 : w ∈ Metric.closedBall (0 : csModel) 2 := closedBall_two_subset_iff' hw
  have hyw : (y : M') = c'.chart w := by
    calc (y : M') = Φ (Φ.symm (y : M')) := (Φ.apply_symm_apply _).symm
      _ = Φ (c.chart w) := by rw [← hweq]
      _ = c'.chart w := hΦ w hw2
  exact y.2 ⟨w, hw, hyw.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.symm_map_mem_interior' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.symm_map_mem_interior'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.symm_map_mem_interior' ``Submission.DifferentialGeometry.Topology.symm_map_mem_interior'

theorem map_mem_interior_right'
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)
    (x : d.interior) : Ψ (x : N) ∈ d'.interior := by
  rw [BallChart.mem_interior]
  rintro ⟨w, hw, hweq⟩
  have hw2 : w ∈ Metric.closedBall (0 : csModel) 2 := closedBall_two_subset_iff' hw
  have hxw : Ψ (x : N) = Ψ (d.chart w) := by
    rw [← hweq]
    exact (hΨ w hw2).symm
  exact x.2 ⟨w, hw, (Ψ.injective hxw).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.map_mem_interior_right' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.map_mem_interior_right'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.map_mem_interior_right' ``Submission.DifferentialGeometry.Topology.map_mem_interior_right'

theorem symm_map_mem_interior_right'
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)
    (y : d'.interior) : Ψ.symm (y : N') ∈ d.interior := by
  rw [BallChart.mem_interior]
  rintro ⟨w, hw, hweq⟩
  have hw2 : w ∈ Metric.closedBall (0 : csModel) 2 := closedBall_two_subset_iff' hw
  have hyw : (y : N') = d'.chart w := by
    calc (y : N') = Ψ (Ψ.symm (y : N')) := (Ψ.apply_symm_apply _).symm
      _ = Ψ (d.chart w) := by rw [← hweq]
      _ = d'.chart w := hΨ w hw2
  exact y.2 ⟨w, hw, hyw.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.symm_map_mem_interior_right' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.symm_map_mem_interior_right'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.symm_map_mem_interior_right' ``Submission.DifferentialGeometry.Topology.symm_map_mem_interior_right'

omit [T2Space N] [T2Space N'] in
theorem csTransport_interiorLeft
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)
    (x : c.interior) :
    csTransport c c' d d' aD Φ Ψ hΦ hΨ (interiorLeft c d aD x)
      = interiorLeft c' d' aD ⟨Φ (x : M), map_mem_interior' c c' Φ hΦ x⟩ := by
  rw [interiorLeft, Function.comp_apply, csTransport_inl]
  refine congrArg (inl c' d' aD.toHomeomorph) (Subtype.ext ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csTransport_interiorLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csTransport_interiorLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csTransport_interiorLeft ``Submission.DifferentialGeometry.Topology.csTransport_interiorLeft

omit [T2Space M] [T2Space M'] in
theorem csTransport_interiorRight
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)
    (x : d.interior) :
    csTransport c c' d d' aD Φ Ψ hΦ hΨ (interiorRight c d aD x)
      = interiorRight c' d' aD ⟨Ψ (x : N), map_mem_interior_right' d d' Ψ hΨ x⟩ := by
  rw [interiorRight, Function.comp_apply, csTransport_inr]
  refine congrArg (inr c' d' aD.toHomeomorph) (Subtype.ext ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csTransport_interiorRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csTransport_interiorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csTransport_interiorRight ``Submission.DifferentialGeometry.Topology.csTransport_interiorRight

end Interior

section Collar

variable {M : Type u} [TopologicalSpace M] [ChartedSpace csModel M]
  {M' : Type u'} [TopologicalSpace M'] [ChartedSpace csModel M']
  {N : Type v} [TopologicalSpace N] [ChartedSpace csModel N]
  {N' : Type v'} [TopologicalSpace N'] [ChartedSpace csModel N']

variable (c : BallChart 3 (𝓡 3) M) (c' : BallChart 3 (𝓡 3) M')
variable (d : BallChart 3 (𝓡 3) N) (d' : BallChart 3 (𝓡 3) N')
variable (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
variable (Φ : M ≃ₜ M') (Ψ : N ≃ₜ N')
variable (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
variable (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)

theorem norm_radial_le (z : csSphere) {r : ℝ} (hr : 0 ≤ r) :
    ‖r • (z : csModel)‖ = r := BallChart.norm_radial z hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.norm_radial_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.norm_radial_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.norm_radial_le ``Submission.DifferentialGeometry.Topology.norm_radial_le

theorem csTransport_collarMap
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Φ (c.chart x) = c'.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 → Ψ (d.chart x) = d'.chart x)
    (p : CollarDomain) :
    csTransport c c' d d' aD Φ Ψ hΦ hΨ (collarMap c d aD p) = collarMap c' d' aD p := by
  rcases p with ⟨z, t⟩
  by_cases ht : 0 ≤ (t : ℝ)
  · rw [collarMap_of_nonneg c d aD _ ht, collarMap_of_nonneg c' d' aD _ ht, csTransport_inl]
    refine congrArg (inl c' d' aD.toHomeomorph) (Subtype.ext ?_)
    have hmem : (1 + (t : ℝ)) • (z : csModel) ∈ Metric.closedBall (0 : csModel) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_radial_le z (by linarith [t.2.1])]
      linarith [t.2.2]
    rw [puncturedHomeomorphOfImage_val]
    exact hΦ _ hmem
  · rw [collarMap_of_neg c d aD _ (lt_of_not_ge ht),
      collarMap_of_neg c' d' aD _ (lt_of_not_ge ht), csTransport_inr]
    refine congrArg (inr c' d' aD.toHomeomorph) (Subtype.ext ?_)
    have hmem : (1 - (t : ℝ)) • (aD z : csModel) ∈ Metric.closedBall (0 : csModel) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_radial_le _ (by linarith [t.2.2])]
      linarith [t.2.1]
    rw [puncturedHomeomorphOfImage_val]
    exact hΨ _ hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csTransport_collarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csTransport_collarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csTransport_collarMap ``Submission.DifferentialGeometry.Topology.csTransport_collarMap


end Collar

section LocalDiff

variable {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{u'} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3} {N' : ConnectedClosedOrientedManifold.{v'} 3}
variable (c : OrientedBallChart M.toClosedOrientedManifold)
variable (c' : OrientedBallChart M'.toClosedOrientedManifold)
variable (d : OrientedBallChart N.toClosedOrientedManifold)
variable (d' : OrientedBallChart N'.toClosedOrientedManifold)
variable (a : BoundaryAttachment)
variable (Φd : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
  (Ψd : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N'.Carrier)
variable (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
  Φd.toHomeomorph (c.toBallChart.chart x) = c'.toBallChart.chart x)
variable (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
  Ψd.toHomeomorph (d.toBallChart.chart x) = d'.toBallChart.chart x)

theorem isLocalDiffeomorph_csTransport :
    letI := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
    letI := csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
        Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ) := by
  let _ : ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
  let _ : ChartedSpace csModel (ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
    csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
    csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
  intro z
  rcases interior_collar_cover c.toBallChart d.toBallChart a.1 z with ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨p, rfl⟩
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (interiorLeft c.toBallChart d.toBallChart a.1) u :=
      (smoothConnectedSum M N c d a).interiorLeft_localDiffeomorph u
    have hΦint : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.toBallChart.interior =>
          (⟨Φd.toHomeomorph (x : M.Carrier),
            map_mem_interior' c.toBallChart c'.toBallChart Φd.toHomeomorph hΦ x⟩ :
              c'.toBallChart.interior)) u :=
      isLocalDiffeomorph_subtypeMap Φd c.toBallChart.interior c'.toBallChart.interior
        (map_mem_interior' c.toBallChart c'.toBallChart Φd.toHomeomorph hΦ)
        (symm_map_mem_interior' c.toBallChart c'.toBallChart Φd.toHomeomorph hΦ) u
    have hcomposite : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.toBallChart.interior =>
          interiorLeft c'.toBallChart d'.toBallChart a.1
            (⟨Φd.toHomeomorph (x : M.Carrier),
              map_mem_interior' c.toBallChart c'.toBallChart Φd.toHomeomorph hΦ x⟩ :
                c'.toBallChart.interior)) u :=
      hΦint.comp (K := 𝓡 3)
        (P := ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph)
        ((smoothConnectedSum M' N' c' d' a).interiorLeft_localDiffeomorph
          (⟨Φd.toHomeomorph (u : M.Carrier),
            map_mem_interior' c.toBallChart c'.toBallChart Φd.toHomeomorph hΦ u⟩ :
              c'.toBallChart.interior))
    have hEq : (fun x : c.toBallChart.interior =>
        csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
          Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (interiorLeft c.toBallChart d.toBallChart a.1 x))
        = fun x : c.toBallChart.interior =>
          interiorLeft c'.toBallChart d'.toBallChart a.1
            (⟨Φd.toHomeomorph (x : M.Carrier),
              map_mem_interior' c.toBallChart c'.toBallChart Φd.toHomeomorph hΦ x⟩ :
                c'.toBallChart.interior) := by
      funext x
      exact csTransport_interiorLeft c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
        a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ x
    have hFcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.toBallChart.interior =>
          csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
            Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
            (interiorLeft c.toBallChart d.toBallChart a.1 x)) u := hEq ▸ hcomposite
    have hpt : hg.localInverse (interiorLeft c.toBallChart d.toBallChart a.1 u) = u :=
      hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : c.toBallChart.interior =>
          csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
            Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
            (interiorLeft c.toBallChart d.toBallChart a.1 x))
        (hg.localInverse (interiorLeft c.toBallChart d.toBallChart a.1 u)) :=
      (by rw [hpt]; exact hFcomp)
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
          a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (interiorLeft c.toBallChart d.toBallChart a.1 (hg.localInverse y)))
        (interiorLeft c.toBallChart d.toBallChart a.1 u) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    simpa only [Function.comp_apply, id_eq] using
      (congrArg (csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
        a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ) hy).symm
  · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (interiorRight c.toBallChart d.toBallChart a.1) v :=
      (smoothConnectedSum M N c d a).interiorRight_localDiffeomorph v
    have hΨint : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.toBallChart.interior =>
          (⟨Ψd.toHomeomorph (x : N.Carrier),
            map_mem_interior_right' d.toBallChart d'.toBallChart Ψd.toHomeomorph hΨ x⟩ :
              d'.toBallChart.interior)) v :=
      isLocalDiffeomorph_subtypeMap Ψd d.toBallChart.interior d'.toBallChart.interior
        (map_mem_interior_right' d.toBallChart d'.toBallChart Ψd.toHomeomorph hΨ)
        (symm_map_mem_interior_right' d.toBallChart d'.toBallChart Ψd.toHomeomorph hΨ) v
    have hcomposite : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.toBallChart.interior =>
          interiorRight c'.toBallChart d'.toBallChart a.1
            (⟨Ψd.toHomeomorph (x : N.Carrier),
              map_mem_interior_right' d.toBallChart d'.toBallChart Ψd.toHomeomorph hΨ x⟩ :
                d'.toBallChart.interior)) v :=
      hΨint.comp (K := 𝓡 3)
        (P := ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph)
        ((smoothConnectedSum M' N' c' d' a).interiorRight_localDiffeomorph
          (⟨Ψd.toHomeomorph (v : N.Carrier),
            map_mem_interior_right' d.toBallChart d'.toBallChart Ψd.toHomeomorph hΨ v⟩ :
              d'.toBallChart.interior))
    have hEq : (fun x : d.toBallChart.interior =>
        csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
          Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (interiorRight c.toBallChart d.toBallChart a.1 x))
        = fun x : d.toBallChart.interior =>
          interiorRight c'.toBallChart d'.toBallChart a.1
            (⟨Ψd.toHomeomorph (x : N.Carrier),
              map_mem_interior_right' d.toBallChart d'.toBallChart Ψd.toHomeomorph hΨ x⟩ :
                d'.toBallChart.interior) := by
      funext x
      exact csTransport_interiorRight c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
        a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ x
    have hFcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.toBallChart.interior =>
          csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
            Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
            (interiorRight c.toBallChart d.toBallChart a.1 x)) v := hEq ▸ hcomposite
    have hpt : hg.localInverse (interiorRight c.toBallChart d.toBallChart a.1 v) = v :=
      hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun x : d.toBallChart.interior =>
          csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
            Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
            (interiorRight c.toBallChart d.toBallChart a.1 x))
        (hg.localInverse (interiorRight c.toBallChart d.toBallChart a.1 v)) :=
      (by rw [hpt]; exact hFcomp)
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
          a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (interiorRight c.toBallChart d.toBallChart a.1 (hg.localInverse y)))
        (interiorRight c.toBallChart d.toBallChart a.1 v) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    simpa only [Function.comp_apply, id_eq] using
      (congrArg (csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
        a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ) hy).symm
  · have hg : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (collarMap c.toBallChart d.toBallChart a.1) p :=
      (smoothConnectedSum M N c d a).collar_localDiffeomorph p
    have hEq : (fun x => csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
          a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (collarMap c.toBallChart d.toBallChart a.1 x))
        = fun x => collarMap c'.toBallChart d'.toBallChart a.1 x :=
      funext fun x => csTransport_collarMap c.toBallChart c'.toBallChart d.toBallChart
        d'.toBallChart a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ x
    have hFcomp : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
          a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (collarMap c.toBallChart d.toBallChart a.1 x)) p := by
      rw [hEq]
      exact (smoothConnectedSum M' N' c' d' a).collar_localDiffeomorph p
    have hpt : hg.localInverse (collarMap c.toBallChart d.toBallChart a.1 p) = p :=
      hg.localInverse_left_inv hg.localInverse_mem_target
    have hFcomp' : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun x => csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
          a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (collarMap c.toBallChart d.toBallChart a.1 x))
        (hg.localInverse (collarMap c.toBallChart d.toBallChart a.1 p)) :=
      (by rw [hpt]; exact hFcomp)
    have h2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
          a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ
          (collarMap c.toBallChart d.toBallChart a.1 (hg.localInverse y)))
        (collarMap c.toBallChart d.toBallChart a.1 p) :=
      (hg.localInverse_isLocalDiffeomorphAt).comp (K := 𝓡 3)
        (P := ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) hFcomp'
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h2
    filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
    simpa only [Function.comp_apply, id_eq] using
      (congrArg (csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
        a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ) hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorph_csTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorph_csTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorph_csTransport ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_csTransport

theorem csTransportDiffeomorph
    (Φd : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier) (Ψd : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N'.Carrier)
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
      Φd.toHomeomorph (c.toBallChart.chart x) = c'.toBallChart.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
      Ψd.toHomeomorph (d.toBallChart.chart x) = d'.toBallChart.chart x) :
    letI := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
    letI := csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) := by
  let _ : ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
  let _ : ChartedSpace csModel (ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
    csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
    csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
  exact ⟨IsLocalDiffeomorph.diffeomorphOfBijective
    (isLocalDiffeomorph_csTransport c c' d d' a Φd Ψd hΦ hΨ)
    (csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
      Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ).bijective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csTransportDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csTransportDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csTransportDiffeomorph ``Submission.DifferentialGeometry.Topology.csTransportDiffeomorph

end LocalDiff
end DifferentialGeometry.Topology
