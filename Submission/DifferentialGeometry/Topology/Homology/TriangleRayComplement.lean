import Submission.DifferentialGeometry.Topology.Homotopy.RayComplement
import Mathlib.Topology.Clopen
import Submission.DifferentialGeometry.Topology.Homology.LiftedSphere
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubspaceCarriers

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.ContinuousMap

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

abbrev puncturedPlane := ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlane ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlane

def planeNegativeDiagonalRayComplement : Set (liftedSphereSpace.{u} 0) :=
  {x | ¬ ∃ r : ℝ, r ≤ 0 ∧ ∀ i : Fin 2, x.down i = r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement

def planePositiveDiagonalRayComplement : Set (liftedSphereSpace.{u} 0) :=
  {x | ¬ ∃ r : ℝ, 0 ≤ r ∧ ∀ i : Fin 2, x.down i = r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement

def puncturedPlanePositiveRayComplement : Set puncturedPlane.{u} :=
  {x | x.val ∈ planePositiveDiagonalRayComplement}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement

def puncturedPlaneNegativeRayComplement : Set puncturedPlane.{u} :=
  {x | x.val ∈ planeNegativeDiagonalRayComplement}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement

private def planeDiagonalVector : liftedSphereSpace.{u} 0 :=
  ULift.up (WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planeDiagonalVector
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planeDiagonalVector target :: scope.openDecls } }

private theorem planeDiagonalVector_ne_zero : planeDiagonalVector.{u} ≠ 0 := by
  intro h
  have hc := congrArg (fun x : liftedSphereSpace.{u} 0 => x.down 0) h
  norm_num [planeDiagonalVector] at hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planeDiagonalVector_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planeDiagonalVector_ne_zero target :: scope.openDecls } }

private theorem planeNegativeDiagonalRayComplement_eq :
    planeNegativeDiagonalRayComplement.{u} =
      (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • planeDiagonalVector) := by
  ext x
  apply not_congr
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨-r, by linarith, ?_⟩
    apply ULift.ext
    ext i
    change x.down i = -(-r) * 1
    rw [hx]
    ring
  · rintro ⟨c, hc, rfl⟩
    exact ⟨-c, by linarith, fun i => by simp [planeDiagonalVector]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement_eq target :: scope.openDecls } }

private theorem planePositiveDiagonalRayComplement_eq :
    planePositiveDiagonalRayComplement.{u} =
      (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • (-planeDiagonalVector)) := by
  ext x
  apply not_congr
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨r, hr, ?_⟩
    apply ULift.ext
    ext i
    change x.down i = (-r) * (-1)
    rw [hx]
    ring
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, fun i => by simp [planeDiagonalVector]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement_eq target :: scope.openDecls } }

private theorem planeNegativeDiagonalRayComplement_ne_zero
    (x : planeNegativeDiagonalRayComplement.{u}) : x.val ≠ 0 := by
  intro h
  exact x.property ⟨0, le_rfl, by rw [h]; exact fun _ => rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planeNegativeDiagonalRayComplement_ne_zero target :: scope.openDecls } }

private theorem planePositiveDiagonalRayComplement_ne_zero
    (x : planePositiveDiagonalRayComplement.{u}) : x.val ≠ 0 := by
  intro h
  exact x.property ⟨0, le_rfl, by rw [h]; exact fun _ => rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planePositiveDiagonalRayComplement_ne_zero target :: scope.openDecls } }

private def planeNegativeRayPuncturedHomeomorph :
    puncturedPlaneNegativeRayComplement.{u} ≃ₜ planeNegativeDiagonalRayComplement.{u} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, planeNegativeDiagonalRayComplement_ne_zero x⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planeNegativeRayPuncturedHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planeNegativeRayPuncturedHomeomorph target :: scope.openDecls } }

private def planePositiveRayPuncturedHomeomorph :
    puncturedPlanePositiveRayComplement.{u} ≃ₜ planePositiveDiagonalRayComplement.{u} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, planePositiveDiagonalRayComplement_ne_zero x⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.planePositiveRayPuncturedHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.planePositiveRayPuncturedHomeomorph target :: scope.openDecls } }

theorem puncturedPlaneNegativeRayComplement_contractibleSpace :
    ContractibleSpace puncturedPlaneNegativeRayComplement.{u} := by
  have : ContractibleSpace planeNegativeDiagonalRayComplement.{u} := by
    rw [planeNegativeDiagonalRayComplement_eq]
    exact contractibleSpace_compl_nonpositive_ray planeDiagonalVector planeDiagonalVector_ne_zero
  exact planeNegativeRayPuncturedHomeomorph.contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement_contractibleSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement_contractibleSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement_contractibleSpace ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneNegativeRayComplement_contractibleSpace

theorem puncturedPlanePositiveRayComplement_contractibleSpace :
    ContractibleSpace puncturedPlanePositiveRayComplement.{u} := by
  have : ContractibleSpace planePositiveDiagonalRayComplement.{u} := by
    rw [planePositiveDiagonalRayComplement_eq]
    exact contractibleSpace_compl_nonpositive_ray (-planeDiagonalVector) (neg_ne_zero.mpr planeDiagonalVector_ne_zero)
  exact planePositiveRayPuncturedHomeomorph.contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement_contractibleSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement_contractibleSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement_contractibleSpace ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlanePositiveRayComplement_contractibleSpace


private theorem isClosed_plane_diagonal :
    IsClosed (Set.ofPred fun x : liftedSphereSpace.{u} 0 =>
      ∀ i : Fin 2, x.down i = x.down 0) := by
  have hc (i : Fin 2) : Continuous (fun x : liftedSphereSpace.{u} 0 => x.down i) := by fun_prop
  have heq : (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ∀ i : Fin 2,
      x.down i = x.down 0) = ⋂ i, {y | y.down i = y.down 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_eq (hc i) (hc 0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.isClosed_plane_diagonal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.isClosed_plane_diagonal target :: scope.openDecls } }

theorem isOpen_planeNegativeDiagonalRayComplement :
    IsOpen planeNegativeDiagonalRayComplement.{u} := by
  have he : planeNegativeDiagonalRayComplement.{u} =
      ((Set.ofPred fun x : liftedSphereSpace.{u} 0 => x.down 0 ≤ 0) ∩
        (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ∀ i : Fin 2, x.down i = x.down 0))ᶜ := by
    ext x
    apply not_congr
    constructor
    · rintro ⟨r, hr, hx⟩
      exact ⟨by change x.down 0 ≤ 0; rw [hx]; exact hr, fun i => (hx i).trans (hx 0).symm⟩
    · rintro ⟨h, hx⟩
      exact ⟨x.down 0, h, hx⟩
  rw [he]
  exact ((isClosed_le (show Continuous (fun x : liftedSphereSpace.{u} 0 => x.down 0) by
    fun_prop) continuous_const).inter isClosed_plane_diagonal).isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.isOpen_planeNegativeDiagonalRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.isOpen_planeNegativeDiagonalRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.isOpen_planeNegativeDiagonalRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.isOpen_planeNegativeDiagonalRayComplement

theorem isOpen_planePositiveDiagonalRayComplement :
    IsOpen planePositiveDiagonalRayComplement.{u} := by
  have he : planePositiveDiagonalRayComplement.{u} =
      ((Set.ofPred fun x : liftedSphereSpace.{u} 0 => 0 ≤ x.down 0) ∩
        (Set.ofPred fun x : liftedSphereSpace.{u} 0 => ∀ i : Fin 2, x.down i = x.down 0))ᶜ := by
    ext x
    apply not_congr
    constructor
    · rintro ⟨r, hr, hx⟩
      exact ⟨by change 0 ≤ x.down 0; rw [hx]; exact hr, fun i => (hx i).trans (hx 0).symm⟩
    · rintro ⟨h, hx⟩
      exact ⟨x.down 0, h, hx⟩
  rw [he]
  exact ((isClosed_le continuous_const (show Continuous (fun x : liftedSphereSpace.{u} 0 => x.down 0) by
    fun_prop)).inter isClosed_plane_diagonal).isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.isOpen_planePositiveDiagonalRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.isOpen_planePositiveDiagonalRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.isOpen_planePositiveDiagonalRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.isOpen_planePositiveDiagonalRayComplement

theorem isOpen_puncturedPlaneNegativeRayComplement : IsOpen puncturedPlaneNegativeRayComplement.{u} :=
  isOpen_planeNegativeDiagonalRayComplement.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlaneNegativeRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlaneNegativeRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlaneNegativeRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlaneNegativeRayComplement

theorem isOpen_puncturedPlanePositiveRayComplement : IsOpen puncturedPlanePositiveRayComplement.{u} :=
  isOpen_planePositiveDiagonalRayComplement.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlanePositiveRayComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlanePositiveRayComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlanePositiveRayComplement ``Submission.DifferentialGeometry.Topology.SimplexDegree.isOpen_puncturedPlanePositiveRayComplement

theorem puncturedPlaneRayComplements_cover :
    puncturedPlanePositiveRayComplement.{u} ∪ puncturedPlaneNegativeRayComplement = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra h
  have hp : ¬ x ∈ puncturedPlanePositiveRayComplement := fun hx => h (Or.inl hx)
  have hn : ¬ x ∈ puncturedPlaneNegativeRayComplement := fun hx => h (Or.inr hx)
  obtain ⟨r, hr, hx⟩ := Classical.not_not.mp hp
  obtain ⟨s, hs, hy⟩ := Classical.not_not.mp hn
  have hrs : r = s := (hx 0).symm.trans (hy 0)
  have hr0 : r = 0 := by linarith
  apply x.property
  apply ULift.ext
  ext i
  exact (hx i).trans hr0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayComplements_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayComplements_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayComplements_cover ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayComplements_cover


theorem puncturedPlaneRayOverlap_coordinate_ne
    (x : subspaceIntersection puncturedPlanePositiveRayComplement.{u}
      puncturedPlaneNegativeRayComplement) :
    x.val.val.val.down 0 ≠ x.val.val.val.down 1 := by
  intro h
  have he (i : Fin 2) : x.val.val.val.down i = x.val.val.val.down 0 := by
    fin_cases i
    · rfl
    · exact h.symm
  rcases le_total (0 : ℝ) (x.val.val.val.down 0) with hp | hn
  · exact x.property ⟨x.val.val.val.down 0, hp, he⟩
  · exact x.val.property ⟨x.val.val.val.down 0, hn, he⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlap_coordinate_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlap_coordinate_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlap_coordinate_ne ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlap_coordinate_ne

private theorem continuous_decide_lt_of_ne {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hne : ∀ x, f x ≠ g x) :
    Continuous (fun x => _root_.Decidable.decide (f x < g x)) := by
  rw [continuous_bool_rng _root_.Bool.true]
  have hset : (fun x => _root_.Decidable.decide (f x < g x)) ⁻¹' {_root_.Bool.true} = {x | f x < g x} := by
    ext x
    simp
  rw [hset]
  constructor
  · have hlt : {x | f x < g x} = {x | f x ≤ g x} := by
      ext x
      exact lt_iff_le_and_ne.trans (and_iff_left (hne x))
    rw [hlt]
    exact isClosed_le hf hg
  · exact isOpen_lt hf hg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.continuous_decide_lt_of_ne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.continuous_decide_lt_of_ne target :: scope.openDecls } }

def puncturedPlaneRayOverlapSign :
    C(subspaceIntersection puncturedPlanePositiveRayComplement.{u}
      puncturedPlaneNegativeRayComplement, ULift.{u} Bool) where
  toFun x := ULift.up (_root_.Decidable.decide (x.val.val.val.down 0 < x.val.val.val.down 1))
  continuous_toFun := continuous_uliftUp.comp (continuous_decide_lt_of_ne
    (by fun_prop) (by fun_prop) puncturedPlaneRayOverlap_coordinate_ne)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign

theorem puncturedPlaneRayOverlapSign_apply
    (x : subspaceIntersection puncturedPlanePositiveRayComplement.{u}
      puncturedPlaneNegativeRayComplement) :
    puncturedPlaneRayOverlapSign x =
      ULift.up (_root_.Decidable.decide (x.val.val.val.down 0 < x.val.val.val.down 1)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign_apply ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneRayOverlapSign_apply

end DifferentialGeometry.Topology.SimplexDegree
