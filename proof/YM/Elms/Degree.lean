import YM.Elms.Spectral
/-! # Spelling with root covariance and finite orbit. All transformations on actual label fibers. No section choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker ComplexOrder
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Civic
open QCD.Kites Beacon PrismD
local notation "τ"=> su.probHaar
def gways (u:su.El)(n:Side) : Frame n:=fun _=>u
-- transform anticomm; shared all.Delta.M.Account
noncomputable def whereby (u:su.El):Drape→ₗ[ℂ] Drape where
   toFun x:= fun n o=> Lat.transform (gways u n) (x n o)
   map_add' x y:= funext (fun i=>funext (fun o=> ContinuousMap.ext (fun U=> map_add (Lat.slots 6 _) ..)))
   map_smul' c x:= funext (fun i=>funext (fun o=> ContinuousMap.ext (fun U=> map_smul (Lat.slots 6 (gways u i)) c _)))
lemma whereby_prod (u:su.El)(x y:Drape): whereby u (x*y)= whereby u x* whereby u y:=funext fun n=>funext fun o=> ContinuousMap.ext (fun U=>map_mul (Lat.slots 6 (gways u n)) _ _)
def Roots (x:Drape) := ∀ (n:Side)(o:Cover)(g:Frame n), Lat.transform g (x n o)= whereby (g (wrap n o)) x n o
noncomputable def OrbitW (x:Drape):Submodule ℂ Drape:= Submodule.span ℂ (Set.range (fun u:su.El=> whereby u x))
def Fins (x:Drape):Prop:= (OrbitW x).FG
def grooming : Submodule ℂ Drape where
    carrier := {x| Roots x}
    zero_mem':=by intro n o g; apply ContinuousMap.ext; intro; rw [map_zero]; exact map_zero (Lat.slots 6 _)
    add_mem':=by intro x y hx hy n o g; apply ContinuousMap.ext; intro U; rw [map_add]; change slots _ _ ((x n o+y n o) _)=_; rw [ContinuousMap.add_apply,map_add]; exact congr_arg₂ (·+·) (DFunLike.congr_fun (hx n o g) U) (DFunLike.congr_fun (hy n o g) U)
    smul_mem':=by intro c x hx n o g; apply ContinuousMap.ext; intro U; rw [map_smul]; change slots _ _ ((c • x n o) _)=_; rw [ContinuousMap.smul_apply,map_smul]; exact congr_arg (c • ·) (DFunLike.congr_fun (hx n o g) U)
lemma Roots.mul {x y : Drape}(hx:Roots x)(hy:Roots y):Roots (x*y):=by
    intro n o g; apply ContinuousMap.ext; intro U; rw [whereby_prod]; change slots _ _ ((x n o*y n o) _)=_; rw [ContinuousMap.mul_apply,map_mul]; exact congr_arg₂ (·*·) (DFunLike.congr_fun (hx n o g) U) (DFunLike.congr_fun (hy n o g) U)
lemma flares (f g:Frame n)(X:Insertion n 6): Lat.transform f (Lat.transform g X)=Lat.transform (g*f) X:=by
    apply ContinuousMap.ext; intro U; have he: Lattice.gauge g (Lattice.gauge f U)=Lattice.gauge (g*f) U:=by funext v; unfold Lattice.gauge; simp only [Pi.mul_apply, mul_inv_rev]; group
    have hp:Lat.rotates 6 g* Lat.rotates 6 f=Lat.rotates 6 (g*f):=by
       unfold Lat.rotates siteRot; rw [← copies_mul,ride_mul]; simp_rw [Equiv.refl_trans, Equiv.refl_apply,Lat.touch_mul, ← Lat.colour_mul]; rfl
    change slots 6 f (slots 6 g (X _))=_; unfold slots; rw [he,adapt_together,hp, ← Matrix.transpose_mul,← star_mul,hp]; rfl
lemma slots_one(X:Insertion n 6): Lat.transform 1 X=X:=by
    apply ContinuousMap.ext; intro U; have he:Lat.rotates 6 (1:Frame n)=1:=by unfold Lat.rotates siteRot; simp_rw [Pi.one_apply,show Lat.colour 1=1 from su.mat_one,Lat.touch_one]; rw [ridden,copies_one]
    have hg: Lattice.gauge 1 U=U:=by funext i; simp [Lattice.gauge]
    change adapter _ _ (X _)=_; rw [hg,he,star_one,Matrix.transpose_one,adapt_one]
lemma twiceR (f g:su.El)(X:Drape): whereby f (whereby g X) = whereby (g*f) X := funext fun n=>funext fun o=> flares (gways f n) (gways g n) (X n o)
lemma whereby_self (x:Drape) : whereby 1 x=x:=funext fun n=>funext fun o=>slots_one (x n o)
lemma outsideA (x:Drape)(u:su.El): whereby u x∈OrbitW x:=Submodule.subset_span ⟨u,rfl⟩
lemma tintedR (x:Drape)(g:su.El)(h:Roots x): Roots (whereby g x):=by
    intro n o k; change Lat.transform k (Lat.transform (gways g n) (x n o))=_; rw [flares, h n o, twiceR]; rfl
-- use explicit finite expansions helpful ensuring Draft. Root orbit.W contains arbitrary shapes.
structure Writing (x:Drape)(g s:ℕ):Prop where
    root : Roots x
    film : Fins x
    draws : ∀ u:su.El,Draft (whereby u x) g s
variable {X Y:Drape}{g s l m:ℕ}
set_option synthInstance.maxHeartbeats 300000 in
lemma Fins.of_span {S:Submodule ℂ Drape}(h : S.FG)(hv:∀ u:su.El, whereby u X∈ S): Fins X:=by
    haveI:Module.Finite ℂ S:= Module.Finite.of_fg h; have hh:OrbitW X ≤ S:= Submodule.span_le.mpr (by rintro _ ⟨p,hp⟩; exact hp ▸ hv p); exact Module.Finite.iff_fg.mp (by apply FiniteDimensional.of_injective (Submodule.inclusion hh) (Submodule.inclusion_injective hh)) -- `fg` name
lemma Writing.add (h:Writing X g s)(hx:Writing Y g s): Writing (X+Y) g s:=by
   refine ⟨grooming.add_mem (show X∈grooming from h.root) (show Y∈grooming from hx.root), ?_,fun u=>by rw [map_add]; exact Draft.joins (h.draws u) (hx.draws u)⟩; apply Fins.of_span (Submodule.FG.sup h.film hx.film); intro u; rw [map_add]; exact Submodule.add_mem _ (show whereby u X∈ OrbitW X⊔ OrbitW Y from Submodule.mem_sup_left (outsideA X u)) (Submodule.mem_sup_right (outsideA Y u))
lemma Writing.scale (h:Writing X g s)(c:ℂ): Writing (c • X) g s:=⟨grooming.smul_mem _ (show X∈ grooming from h.root), Fins.of_span h.film (fun u=>by rw [map_smul]; exact Submodule.smul_mem _ _ (outsideA X u)),fun u=>by rw [map_smul]; exact Draft.scale (h.draws u) c⟩
lemma Writing.neg (h:Writing X g s): Writing (-X) g s:=by simpa using h.scale (-1)
lemma Writing.sub (h:Writing X g s)(hx:Writing Y g s): Writing (X-Y) g s:=by rw [sub_eq_add_neg]; exact h.add hx.neg
lemma Writing.zero (g s:ℕ): Writing 0 g s:= ⟨grooming.zero_mem, Fins.of_span (show (⊥ : Submodule ℂ Drape).FG from Submodule.fg_bot) (fun u=>by simp),fun u=>by rw [map_zero]; exact drought ..⟩
lemma Writing.mul (h:Writing X g s)(hp:Writing Y l m):Writing (X*Y) (g+l) (s+m):=⟨ h.root.mul hp.root,Fins.of_span (Submodule.FG.mul h.film hp.film) (fun u=> by rw [whereby_prod]; exact Submodule.mul_mem_mul (outsideA X u) (outsideA Y u)),fun u=>by rw [whereby_prod]; exact (h.draws u).mulX (hp.draws u)⟩
lemma Writing.unit : Writing 1 0 0:=by
   have hp(u:su.El): whereby u 1=1:=funext fun n=>funext fun o=>invariant_one (n:=n) (F:=6) (gways u n)
   refine ⟨?_, Fins.of_span (Submodule.fg_span (Set.finite_singleton (1:Drape))) (fun u=>?_),fun u=> (hp u).symm ▸ birth0⟩
   · intro n o g; rw [hp]; exact invariant_one _
   rw [hp]; exact Submodule.subset_span (s:={(1:Drape)}) (Set.mem_singleton _)
lemma Writing.join {I:Type}(x:Finset I)(P:I→Drape)(h:∀ i∈x, Writing (P i) g s):Writing (∑ i∈x, P i) g s:=by induction x using Finset.induction_on with
    | empty=> rw [sum_empty]; exact Writing.zero ..
    | insert i x hi hx => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (hx fun i hi=>h _ (mem_insert_of_mem hi))
-- compiler for color agitation at any module. Explicit
variable (q:Bool)(i:Dike)(b:su.El)
lemma agitated (f:Frame n): Roots (burnish w q i):=by
    intro n o f; apply ContinuousMap.ext; intro V; exact (flowAct o w V q i f).trans (flowAct o w V q i (gways (f (wrap n o)) n)).symm -- order
lemma shake : whereby b (burnish w q i)=∑ j:Dike, peggle q (clutch b) i j • burnish w q j:=by funext n o; apply ContinuousMap.ext; intro V; simp only [Finset.sum_apply, ContinuousMap.sum_apply]; exact flowAct o w V q i (gways b n)
lemma wroteB : Writing (burnish w q i) 0 1:=by
    let n:Side:=⟨1,by omega⟩; refine ⟨agitated w q i (1:Frame n), Fins.of_span (Submodule.fg_span (Set.finite_range (burnish w q))) (fun u=>?_),fun u=>by rw [shake]; apply Draft.sums; intro i _; exact Draft.scale (brew ..) _⟩; rw [shake]; exact Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩))
end Civic
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Civic.wroteB
