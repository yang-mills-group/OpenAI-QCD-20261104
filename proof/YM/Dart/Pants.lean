import YM.Elms.Corner
import YM.Needle.Vista
import YM.Elms.Plasma
/-! # Immutable (units before bare parameters chosen) support/germ tariff for scale-free words. At every coverage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
-- don't open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PlaneG
variable (S T:Stenc)(o:Cover)(h:S.image (fun i=>i+o) ⊆ T)
noncomputable def edges (i:UsedEdges S):UsedEdges T:=⟨(i.val.1+o, i.val.2),h (mem_image.mpr ⟨_,i.property.1,rfl⟩),h (mem_image.mpr ⟨_,i.property.2,add_right_comm ..⟩)⟩
noncomputable def scopeX (i:YM.Source.Index su S):YM.Source.Index su T:= (edges S T o h i.1,i.2)
noncomputable def spinL (i:Cylinder.Nearest S 6):Cylinder.Nearest T 6:=((⟨i.1.1.val+o,h (mem_image.mpr ⟨_,i.1.1.property,rfl⟩)⟩,i.1.2),i.2)
noncomputable def arm :Matrix (Cylinder.Nearest S 6) (Cylinder.Nearest T 6) ℂ:=Matrix.of fun i j=>if spinL S T o h i=j then 1 else 0
noncomputable def spun :Dirac (Cylinder.Nearest S 6)→ₐ[ℂ]Dirac (Cylinder.Nearest T 6):= adapter (arm S T o h) (arm S T o h)
lemma spin_path {s:ℕ}(x:Dirac (Cylinder.Nearest S 6))(hx:x∈ layer _ s): spun S T o h x∈ layer _ s:= Grass.exterior_layer _ hx
lemma voyage (x:Dirac (Cylinder.Nearest S 6))(b:Cover): tongue (c:=n) T b (spun S T o h x)= tongue S (o+b) x:=by
    let L:=arm S T o h
    have he:L * Ferry.belt n T b= Ferry.belt n S (o+b):=by
         ext i j; change ∑ k, L i k * Ferry.belt n T b k j = _; simp_rw [L,arm,Matrix.of_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq]; simp only [mem_univ,if_true]; unfold Ferry.belt Cylinder.lower; simp only [Matrix.of_apply,spinL,add_assoc]
    -- adapter composition
    unfold tongue spun; rw [adapt_together] -- order
    rw[← show L=arm S T o h from rfl,he]
local notation "Ψ"=>scopeX S T o h
variable (p: Cylinder.Formula S 6)
noncomputable def grow: Cylinder.Formula T 6:= TensorProduct.map (MvPolynomial.rename (R:=ℂ) Ψ).toLinearMap (spun S T o h).toLinearMap p
open Work.G06
noncomputable abbrev turned(V:Land):Land:= fun z=> V (z.1+o,z.2)
lemma lift_e(V:Land): porch T V (grow S T o h p)= spun S T o h (porch S (turned o V) p):=by
    have he(x:Source.Formula su S): MvPolynomial.aeval (Source.entry V) (MvPolynomial.rename Ψ x)=MvPolynomial.aeval (Source.entry (turned o V)) x:=by
       induction x using MvPolynomial.induction_on with
       | C a=> simp
       | add p q hp hq=>rw [map_add,map_add,map_add,hp,hq]
       | mul_X p i ih=> rw [map_mul,map_mul,map_mul,MvPolynomial.rename_X,MvPolynomial.aeval_X,MvPolynomial.aeval_X,ih]; rfl
    induction p using TensorProduct.induction_on with
    | zero=>simp [grow]
    | tmul a b=>rw [grow,TensorProduct.map_tmul,porch_air,porch_air,map_smul,AlgHom.toLinearMap_apply,he]; rfl
    | add a b ih im=>rw [show grow S T o h (a+b)= grow S T o h a + grow S T o h b from map_add (TensorProduct.map _ _) ..,map_add,map_add,map_add,ih,im]
local notation "Γ"=>grow S T o h
noncomputable def fling (a:Cover)(x:Drape):Drape:=fun n b=> x n (a+b)
lemma shoots : grant T (grow S T o h p)=fling o (grant S p):=by
    funext n b; apply ContinuousMap.ext; intro U
    change grant _ _ _ _ _=grant _ _ _ _ _; rw [granting,granting,lift_e,voyage]
    suffices H:turned o (expandAt (wrap n b) U)=expandAt (wrap n (o+b)) U by rw[H]
    funext z; simp only[turned,expandAt,map_add, add_assoc]
lemma naturally (p: Cylinder.Formula S 6)(r k m:ℕ): Lease r k m 0 (fun Y=> porch S Y p):=by
   induction p using TensorProduct.induction_on with
   | zero=> simp_rw[map_zero]; exact Lease.cup _
   | tmul a b=> simp_rw [porch_air]; let L:= ((LinearMap.toSpanSingleton ℂ (Dirac (Cylinder.Nearest S 6)) b).restrictScalars ℝ).toContinuousLinearMap; exact (Permit.ground S (show Work.G06.EntryPoly S (fun i:Land=>MvPolynomial.aeval (Source.entry i) a) from ⟨a,fun _=>rfl⟩) r k m).linear L
   | add p q h hp=>simp_rw[map_add]; exact h.add hp
lemma hooking (s:ℕ)(he:∀ Y:Land,porch S Y p∈layer _ s):Draft (fling o (grant S p)) 0 s:=by
    filter_upwards [eventually_ge_atTop (S.image (fun i=>i+o))] with T h
    refine ⟨grow S T o h p,shoots S T o h p,fun Y=>?_,fun k m r _=>naturally _ _ ..⟩; rw[lift_e]; exact spin_path _ _ _ h _ (he _)
end PlaneG
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PlaneG.hooking
