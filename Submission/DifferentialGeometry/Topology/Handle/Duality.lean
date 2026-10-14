import Submission.DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Topology.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Handle

def swap (k l : ℕ) : StandardHandle k l ≃ₜ StandardHandle l k :=
  Homeomorph.prodComm (X := ClosedCell k) (Y := ClosedCell l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap ``Submission.DifferentialGeometry.Topology.Handle.swap

@[simp]
theorem swap_apply {k l : ℕ} (p : StandardHandle k l) : swap k l p = (p.2, p.1) := by
  simp [swap, Prod.swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_apply ``Submission.DifferentialGeometry.Topology.Handle.swap_apply

theorem swap_swap {k l : ℕ} (p : StandardHandle k l) : swap l k (swap k l p) = p := by
  simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_swap ``Submission.DifferentialGeometry.Topology.Handle.swap_swap

@[simp]
theorem swap_symm {k l : ℕ} : (swap k l).symm = swap l k := by
  simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_symm ``Submission.DifferentialGeometry.Topology.Handle.swap_symm

theorem swap_attachingRegion (k l : ℕ) : swap k l '' attachingRegion k l = beltRegion l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, attachingRegion, beltRegion] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, attachingRegion, beltRegion] using hp
    · simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_attachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_attachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_attachingRegion ``Submission.DifferentialGeometry.Topology.Handle.swap_attachingRegion

theorem swap_beltRegion (k l : ℕ) : swap k l '' beltRegion k l = attachingRegion l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, beltRegion, attachingRegion] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, beltRegion, attachingRegion] using hp
    · simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_beltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_beltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_beltRegion ``Submission.DifferentialGeometry.Topology.Handle.swap_beltRegion

theorem swap_corner (k l : ℕ) : swap k l '' corner k l = corner l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, corner] using And.intro hq.2 hq.1
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, corner] using And.intro hp.2 hp.1
    · simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_corner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_corner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_corner ``Submission.DifferentialGeometry.Topology.Handle.swap_corner

theorem swap_coreDisk (k l : ℕ) : swap k l '' coreDisk k l = cocoreDisk l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, coreDisk, cocoreDisk] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, coreDisk, cocoreDisk] using hp
    · simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_coreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_coreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_coreDisk ``Submission.DifferentialGeometry.Topology.Handle.swap_coreDisk

theorem swap_cocoreDisk (k l : ℕ) : swap k l '' cocoreDisk k l = coreDisk l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, cocoreDisk, coreDisk] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, cocoreDisk, coreDisk] using hp
    · simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_cocoreDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_cocoreDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_cocoreDisk ``Submission.DifferentialGeometry.Topology.Handle.swap_cocoreDisk

theorem swap_attachingSphere (k l : ℕ) : swap k l '' attachingSphere k l = beltSphere l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, attachingSphere, beltSphere] using And.intro hq.2 hq.1
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, attachingSphere, beltSphere] using And.intro hp.2 hp.1
    · simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_attachingSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_attachingSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_attachingSphere ``Submission.DifferentialGeometry.Topology.Handle.swap_attachingSphere

theorem swap_beltSphere (k l : ℕ) : swap k l '' beltSphere k l = attachingSphere l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, beltSphere, attachingSphere] using And.intro hq.2 hq.1
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, beltSphere, attachingSphere] using And.intro hp.2 hp.1
    · simp [swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_beltSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_beltSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_beltSphere ``Submission.DifferentialGeometry.Topology.Handle.swap_beltSphere

theorem swap_attachingInclusion {k l : ℕ} (a : AttachingRegion k l) :
    swap k l (attachingInclusion k l a) = beltInclusion l k (Prod.swap a) := by
  rcases a with ⟨a₁, a₂⟩
  simp [swap, attachingInclusion, beltInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_attachingInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_attachingInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_attachingInclusion ``Submission.DifferentialGeometry.Topology.Handle.swap_attachingInclusion

theorem swap_beltInclusion {k l : ℕ} (a : BeltRegion k l) :
    swap k l (beltInclusion k l a) = attachingInclusion l k (Prod.swap a) := by
  rcases a with ⟨a₁, a₂⟩
  simp [swap, beltInclusion, attachingInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_beltInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_beltInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_beltInclusion ``Submission.DifferentialGeometry.Topology.Handle.swap_beltInclusion

theorem swap_cornerInclusion {k l : ℕ} (a : Corner k l) :
    swap k l (cornerInclusion k l a) = cornerInclusion l k (Prod.swap a) := by
  rcases a with ⟨a₁, a₂⟩
  simp [swap, cornerInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_cornerInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_cornerInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_cornerInclusion ``Submission.DifferentialGeometry.Topology.Handle.swap_cornerInclusion

theorem swap_coreDiskInclusion {k l : ℕ} (x : ClosedCell k) :
    swap k l (coreDiskInclusion k l x) = cocoreDiskInclusion l k x := by
  simp [swap, coreDiskInclusion, cocoreDiskInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_coreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_coreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_coreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.swap_coreDiskInclusion

theorem swap_cocoreDiskInclusion {k l : ℕ} (y : ClosedCell l) :
    swap k l (cocoreDiskInclusion k l y) = coreDiskInclusion l k y := by
  simp [swap, cocoreDiskInclusion, coreDiskInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_cocoreDiskInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_cocoreDiskInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_cocoreDiskInclusion ``Submission.DifferentialGeometry.Topology.Handle.swap_cocoreDiskInclusion

theorem swap_attachingSphereInclusion {k l : ℕ} (x : CellBoundary k) :
    swap k l (attachingSphereInclusion k l x) = beltSphereInclusion l k x := by
  simp [swap, attachingSphereInclusion, beltSphereInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_attachingSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_attachingSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_attachingSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.swap_attachingSphereInclusion

theorem swap_beltSphereInclusion {k l : ℕ} (y : CellBoundary l) :
    swap k l (beltSphereInclusion k l y) = attachingSphereInclusion l k y := by
  simp [swap, beltSphereInclusion, attachingSphereInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_beltSphereInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_beltSphereInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_beltSphereInclusion ``Submission.DifferentialGeometry.Topology.Handle.swap_beltSphereInclusion

private theorem swap_not_mem_core_of_not_mem_cocore {k l : ℕ} {p : StandardHandle k l}
    (hp : p ∉ cocoreDisk k l) : swap k l p ∉ coreDisk l k := by
  intro h
  have hmem : p ∈ cocoreDisk k l := by
    have h' : swap k l p ∈ swap k l '' cocoreDisk k l := by
      rwa [swap_cocoreDisk k l]
    rcases h' with ⟨z, hz, hzswap⟩
    have hz' : z = p := by
      have hz'0 : swap l k (swap k l z) = swap l k (swap k l p) := congrArg (swap l k) hzswap
      simpa [swap_swap] using hz'0
    simpa [hz'] using hz
  exact hp hmem

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.swap_not_mem_core_of_not_mem_cocore
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.swap_not_mem_core_of_not_mem_cocore target :: scope.openDecls } }

private theorem swap_not_mem_cocore_of_not_mem_core {k l : ℕ} {p : StandardHandle k l}
    (hp : p ∉ coreDisk k l) : swap k l p ∉ cocoreDisk l k := by
  intro h
  have hmem : p ∈ coreDisk k l := by
    have h' : swap k l p ∈ swap k l '' coreDisk k l := by
      rwa [swap_coreDisk k l]
    rcases h' with ⟨z, hz, hzswap⟩
    have hz' : z = p := by
      have hz'0 : swap l k (swap k l z) = swap l k (swap k l p) := congrArg (swap l k) hzswap
      simpa [swap_swap] using hz'0
    simpa [hz'] using hz
  exact hp hmem

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.swap_not_mem_cocore_of_not_mem_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.swap_not_mem_cocore_of_not_mem_core target :: scope.openDecls } }

def swapCocoreComplement (k l : ℕ) :
    {p : StandardHandle k l // p ∉ cocoreDisk k l} ≃ₜ
      {p : StandardHandle l k // p ∉ coreDisk l k} where
  toFun := fun p => ⟨swap k l (p : StandardHandle k l), swap_not_mem_core_of_not_mem_cocore p.2⟩
  invFun := fun q => ⟨swap l k (q : StandardHandle l k),
    swap_not_mem_cocore_of_not_mem_core (k := l) (l := k) q.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact swap_swap (p : StandardHandle k l)
  right_inv := by
    intro q
    apply Subtype.ext
    exact swap_swap (q : StandardHandle l k)
  continuous_toFun := Continuous.subtype_mk
    (p := fun r : StandardHandle l k => r ∉ coreDisk l k)
    ((swap k l).continuous.comp continuous_subtype_val) (fun p => swap_not_mem_core_of_not_mem_cocore p.2)
  continuous_invFun := Continuous.subtype_mk
    (p := fun r : StandardHandle k l => r ∉ cocoreDisk k l)
    ((swap l k).continuous.comp continuous_subtype_val)
    (fun q => swap_not_mem_cocore_of_not_mem_core (k := l) (l := k) q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCocoreComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCocoreComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCocoreComplement ``Submission.DifferentialGeometry.Topology.Handle.swapCocoreComplement

def swapCoreComplement (k l : ℕ) :
    {p : StandardHandle k l // p ∉ coreDisk k l} ≃ₜ
      {p : StandardHandle l k // p ∉ cocoreDisk l k} where
  toFun := fun p => ⟨swap k l (p : StandardHandle k l), swap_not_mem_cocore_of_not_mem_core p.2⟩
  invFun := fun q => ⟨swap l k (q : StandardHandle l k),
    swap_not_mem_core_of_not_mem_cocore (k := l) (l := k) q.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact swap_swap (p : StandardHandle k l)
  right_inv := by
    intro q
    apply Subtype.ext
    exact swap_swap (q : StandardHandle l k)
  continuous_toFun := Continuous.subtype_mk
    (p := fun r : StandardHandle l k => r ∉ cocoreDisk l k)
    ((swap k l).continuous.comp continuous_subtype_val) (fun p => swap_not_mem_cocore_of_not_mem_core p.2)
  continuous_invFun := Continuous.subtype_mk
    (p := fun r : StandardHandle k l => r ∉ coreDisk k l)
    ((swap l k).continuous.comp continuous_subtype_val)
    (fun q => swap_not_mem_core_of_not_mem_cocore (k := l) (l := k) q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCoreComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCoreComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCoreComplement ``Submission.DifferentialGeometry.Topology.Handle.swapCoreComplement

def swapCoreCocoreComplement (k l : ℕ) :
    {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} ≃ₜ
      {p : StandardHandle l k // p ∉ coreDisk l k ∧ p ∉ cocoreDisk l k} where
  toFun := fun p => ⟨swap k l (p : StandardHandle k l),
    ⟨swap_not_mem_core_of_not_mem_cocore p.2.2, swap_not_mem_cocore_of_not_mem_core p.2.1⟩⟩
  invFun := fun q => ⟨swap l k (q : StandardHandle l k),
    ⟨swap_not_mem_core_of_not_mem_cocore (k := l) (l := k) q.2.2,
      swap_not_mem_cocore_of_not_mem_core (k := l) (l := k) q.2.1⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact swap_swap (p : StandardHandle k l)
  right_inv := by
    intro q
    apply Subtype.ext
    exact swap_swap (q : StandardHandle l k)
  continuous_toFun := Continuous.subtype_mk
    (p := fun r : StandardHandle l k => r ∉ coreDisk l k ∧ r ∉ cocoreDisk l k)
    ((swap k l).continuous.comp continuous_subtype_val)
    (fun p => ⟨swap_not_mem_core_of_not_mem_cocore p.2.2, swap_not_mem_cocore_of_not_mem_core p.2.1⟩)
  continuous_invFun := Continuous.subtype_mk
    (p := fun r : StandardHandle k l => r ∉ coreDisk k l ∧ r ∉ cocoreDisk k l)
    ((swap l k).continuous.comp continuous_subtype_val)
    (fun q => ⟨swap_not_mem_core_of_not_mem_cocore (k := l) (l := k) q.2.2,
      swap_not_mem_cocore_of_not_mem_core (k := l) (l := k) q.2.1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement ``Submission.DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement

@[simp]
theorem swapCocoreComplement_apply (k l : ℕ)
    (p : {p : StandardHandle k l // p ∉ cocoreDisk k l}) :
    (swapCocoreComplement k l p : StandardHandle l k) = swap k l (p : StandardHandle k l) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCocoreComplement_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCocoreComplement_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCocoreComplement_apply ``Submission.DifferentialGeometry.Topology.Handle.swapCocoreComplement_apply

@[simp]
theorem swapCoreComplement_apply (k l : ℕ)
    (p : {p : StandardHandle k l // p ∉ coreDisk k l}) :
    (swapCoreComplement k l p : StandardHandle l k) = swap k l (p : StandardHandle k l) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCoreComplement_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCoreComplement_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCoreComplement_apply ``Submission.DifferentialGeometry.Topology.Handle.swapCoreComplement_apply

@[simp]
theorem swapCoreCocoreComplement_apply (k l : ℕ)
    (p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l}) :
    (swapCoreCocoreComplement k l p : StandardHandle l k) = swap k l (p : StandardHandle k l) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_apply ``Submission.DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_apply

theorem swapCocoreComplement_symm (k l : ℕ) :
    (swapCocoreComplement k l).symm = swapCoreComplement l k := by
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCocoreComplement_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCocoreComplement_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCocoreComplement_symm ``Submission.DifferentialGeometry.Topology.Handle.swapCocoreComplement_symm

theorem swapCoreComplement_symm (k l : ℕ) :
    (swapCoreComplement k l).symm = swapCocoreComplement l k := by
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCoreComplement_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCoreComplement_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCoreComplement_symm ``Submission.DifferentialGeometry.Topology.Handle.swapCoreComplement_symm

theorem swapCoreCocoreComplement_symm (k l : ℕ) :
    (swapCoreCocoreComplement k l).symm = swapCoreCocoreComplement l k := by
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_symm ``Submission.DifferentialGeometry.Topology.Handle.swapCoreCocoreComplement_symm

theorem swap_attachingInclusion_attachingSphereInclusionAttachingRegion (k l : ℕ)
    (u : CellBoundary k) :
    swap k l (attachingInclusion k l (attachingSphereInclusionAttachingRegion k l u)) =
      beltInclusion l k (beltSphereInclusionBeltRegion l k u) := by
  rw [swap_attachingInclusion]
  simp [attachingSphereInclusionAttachingRegion, beltSphereInclusionBeltRegion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_attachingInclusion_attachingSphereInclusionAttachingRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_attachingInclusion_attachingSphereInclusionAttachingRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_attachingInclusion_attachingSphereInclusionAttachingRegion ``Submission.DifferentialGeometry.Topology.Handle.swap_attachingInclusion_attachingSphereInclusionAttachingRegion

theorem swap_beltInclusion_beltSphereInclusionBeltRegion (k l : ℕ) (v : CellBoundary l) :
    swap k l (beltInclusion k l (beltSphereInclusionBeltRegion k l v)) =
      attachingInclusion l k (attachingSphereInclusionAttachingRegion l k v) := by
  rw [swap_beltInclusion]
  simp [beltSphereInclusionBeltRegion, attachingSphereInclusionAttachingRegion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.swap_beltInclusion_beltSphereInclusionBeltRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.swap_beltInclusion_beltSphereInclusionBeltRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.swap_beltInclusion_beltSphereInclusionBeltRegion ``Submission.DifferentialGeometry.Topology.Handle.swap_beltInclusion_beltSphereInclusionBeltRegion

end DifferentialGeometry.Topology.Handle
