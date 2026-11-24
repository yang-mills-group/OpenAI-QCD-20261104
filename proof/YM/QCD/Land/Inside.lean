import YM.QCD.RP.Yard

/-!
# Local field algebra for infinite lattice spacing-fixed limit

Enlarge finite site sets. Test functions continuous on internal links, take values in
local Grassmann algebra. Full local algebra, with a separate gauge invariant subalgebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Land
open Lat Grass Lattice Wilson RP
open Function
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology

abbrev Lot := Finset Cover
variable {D S P : Lot} {n : Side} {F : ℕ}
abbrev Court (D : Lot) := (D : Type)
abbrev Pipe (D : Lot) := {e : Court D × Axis // e.1.val+step e.2∈D}
abbrev Trace (D : Lot) := Pipe D → su.El
abbrev Pad (D : Lot) (F : ℕ) := (Court D × Fiber) × Flavor F
abbrev Poly (D : Lot) (F : ℕ) := Dirac (Pad D F)
abbrev Cyl (D : Lot) (F : ℕ) := C(Trace D,Poly D F)
instance (D : Lot) (F : ℕ) : CompleteSpace (Cyl D F) := by unfold Cyl; infer_instance
instance (D : Lot) : CompactSpace (Trace D) := by unfold Trace; infer_instance
instance (D : Lot) : BorelSpace (Trace D) := by unfold Trace; infer_instance

def inlet (k : Pipe D) := k.val.1
def drain (k : Pipe D) : Court D := ⟨k.val.1.val+step k.val.2,k.property⟩
def way (k : Pipe D) := k.val.2
lemma drains (k : Pipe D) : (drain k).val=(inlet k).val+step (way k) := rfl

def coveredge (k : Pipe D) : Edge Cover := ((inlet k).val,way k)
def inspects (V : CoverConfig su) : Trace D := fun k => V (coveredge k)
lemma coveredge_inj : Injective (coveredge (D:=D)) := by
  intro i j h; apply Subtype.ext; exact Prod.ext (Subtype.ext (congrArg (fun x => x.1) h)) (congrArg (fun x => x.2) h)
lemma survey : Surjective (inspects (D:=D)) := fun x => by
  refine ⟨Function.extend coveredge x 1, funext fun i => ?_⟩
  exact coveredge_inj.extend_apply ..

def court (h : D ⊆ S) (x : Court D) : Court S := ⟨x.val,h x.property⟩
def plumbing (h : D ⊆ S) (v : Pipe D) : Pipe S := ⟨(court h (inlet v),way v), h v.property⟩
def carries (h : D ⊆ S) (u : Trace S) : Trace D := fun i => u (plumbing h i)
@[fun_prop] lemma carries_cont (h : D ⊆ S) : Continuous (carries h) := by unfold carries; fun_prop

def channel (h : D ⊆ S) (i : Pad D F) : Pad S F := ((court h i.1.1,i.1.2),i.2)

def crowd (h : D ⊆ S) (x : Cyl D F) : Cyl S F :=
  ⟨fun U => pass (channel h) (x (carries h U)),(pass (channel h)).toLinearMap.continuous_of_finiteDimensional.comp (x.continuous.comp (carries_cont h))⟩
@[simp] lemma crowding (h : D ⊆ S) (x : Cyl D F) (U) : crowd h x U=pass (channel h) (x (carries h U)) := rfl
lemma crowd_full (h : D ⊆ S) (x y : Cyl D F) : crowd h (x*y)=crowd h x*crowd h y := by ext1 U; simp
lemma crowd_comp (h : D ⊆ S) (k : S ⊆ P) (x : Cyl D F) : crowd k (crowd h x) = crowd (h.trans k) x := by
  ext1 i; simp only [crowding]; rw [← AlgHom.comp_apply,pass_comp]; rfl
lemma pass_id {X : Type*} [Fintype X] : pass (@id X)=AlgHom.id ℂ _ := ext_atoms (by rintro (i|i) <;> simp [pass])
lemma crowd_id (x : Cyl D F) : crowd (D:=D) (S:=D) (Finset.Subset.refl _) x=x := by
  ext1 U; change pass id (x U)=x U; rw [pass_id]; rfl

def pipeM (n : Side) (i : Pipe D) : Edge (Site n) := (wrap n (coveredge i).1,(coveredge i).2)
def wraps (n : Side) (U : Grid n) : Trace D := fun i => U (pipeM n i)
@[fun_prop] lemma wraps_cont (D : Lot) (n : Side) : Continuous (wraps (D:=D) n) := by unfold wraps; fun_prop
lemma drains_wrap (n : Side) (i : Pipe D) : wrap n (drain i).val=(pipeM n i).1+step (pipeM n i).2 := by rw [drains,map_add,wrap_step]; rfl
lemma inspects_wrap (n : Side) (U : Grid n) : wraps (D:=D) n U=inspects (expandAt 0 U) := by ext1 i; simp only [inspects,coveredge,expandAt,add_zero]; rfl

def allot (n : Side) (i : Pad D F) : Modes n F := ((wrap n i.1.1.val,i.1.2),i.2)

def issue (n : Side) (x : Cyl D F) : Insertion n F := ⟨fun U => pass (allot n) (x (wraps n U)),
  (pass (allot n)).toLinearMap.continuous_of_finiteDimensional.comp (x.continuous.comp (wraps_cont _ n))⟩
@[simp] lemma issued (n : Side) (x : Cyl D F) (U) : issue n x U = pass (allot n) (x (wraps n U)) := rfl
lemma respect (n : Side) (h : D ⊆ S) (x : Cyl D F) : issue n (crowd h x)=issue n x := by
  ext1 i; simp only [issued,crowding]; rw [← AlgHom.comp_apply,pass_comp]; rfl
lemma issue_add (n : Side) (x y : Cyl D F) : issue n (x+y)=issue n x+issue n y := by ext1 U; simp
lemma issue_smul (c : ℂ) (n : Side) (x : Cyl D F) : issue n (c • x)=c • issue n x := by ext1 U; simp
lemma issue_mul (n : Side) (x y : Cyl D F) : issue n (x*y)=issue n x*issue n y := by ext1 U; simp
lemma issue_one (n : Side) (D : Lot) (F : ℕ) : issue n (1:Cyl D F)=1 := by ext1 U; simp

def Fits (n : Side) (D : Lot) : Prop := Set.InjOn (wrap n) ↑D
lemma fuse (h : Fits n D) : Injective (allot (D:=D) (F:=F) n) := by
  intro i j he; apply Prod.ext
  · exact Prod.ext (Subtype.ext (h i.1.1.property j.1.1.property (congrArg (fun x => x.1.1) he))) (congrArg (fun x => x.1.2) he)
  exact congrArg (fun x => x.2) he

lemma pass_price {A B : Type*} [Fintype A] [Fintype B] {f : A → B} (h : Injective f) (x : Dirac A) : ‖pass f x‖ ≤ ‖x‖ :=
  norm_embed_le (⟨Sum.map f f,Sum.map_injective.mpr ⟨h,h⟩⟩) x
lemma issue_price (h : Fits n D) (x : Cyl D F) : ‖issue n x‖ ≤ ‖x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr; intro i; rw [issued]
  exact (pass_price (fuse h) _).trans (ContinuousMap.norm_coe_le_norm x _)

lemma locates (n : Side) (x : Cyl D F) (A : Set (Site n)) (h : Set.MapsTo (wrap n) ↑D A) :
    Floors A (issue n x) := by
  let u : Pad D F → Deck A F := fun i => ((⟨wrap n i.1.1.val,h i.1.1.property⟩,i.1.2),i.2)
  refine ⟨fun i => pass u (x (wraps n i)), (pass u).toLinearMap.continuous_of_finiteDimensional.comp
    (x.continuous.comp (wraps_cont ..)),fun U V H => ?_,fun i => ?_⟩
  · exact congrArg (fun k : Trace D => pass u (x k)) (funext fun j => H _ (h (inlet j).property) ((drains_wrap n j) ▸ h (drain j).property))
  rw [issued,← AlgHom.comp_apply,pass_comp]; rfl
end YM.QCD.Land
