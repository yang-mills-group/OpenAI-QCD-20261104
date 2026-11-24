import YM.Sunda.Hula
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Poised Massive.Poised.Display Massive.Poised.Stative Module Finset Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
variable {d:ℕ}
open Grass.Ward TableT Pane Massive.Poised.Plans.Stamp Lobo
variable (f g a b:Flavor 6)(p q p' q':Multi d)
local notation "Δ"=> Sunda.lamp f g p q
lemma c_bare (M:Spike): Δ (bilinear a b M p' q')= if f=a∧g=b∧p=p'∧q=q' then M else 0:=by
     rw [←j_stard]; unfold lamp; rw [LinearMap.comp_apply,LinearMap.comp_apply]; change ingot (gravel f g p q (skin _ ((1:GPol)⊗ₜ[ℂ]Oriole.coat _)))= _; rw[mintSkin,map_one,one_smul]; have he: gravel f g p q (fieldB a b p' q' (wave M))=if f=a∧g=b∧p=p'∧q=q' then wave M else 0:=by
           ext i j; change fieldB _ _ _ _ _ ((p,i),f) ((q,j),g)=_; rw[fieldK]; simp only; by_cases h:f=a∧g=b∧p=p'∧q=q'; · rw[if_pos h,if_pos (by tauto)]
           rw[if_neg h,if_neg (by tauto)]; rfl
     rw [he]; split_ifs; exact Stew.leafy _; exact map_zero _
lemma leary(x:GPol): Δ (plain d x)=0:=by unfold lamp; rw [LinearMap.comp_apply,LinearMap.comp_apply,plainP,unit_skin,map_zero,map_zero]
lemma fogBA(M:Spike): fog (bilinear a b M p q)=0:=by rw [← j_stard]; exact mintFog ..
-- weighted homogeneous no low gauge except 1
open Extra.WeakScaling.Color
lemma unitMine {d:ℕ}(hd:d<4)(u:Labels.Label su d) : ∃ z:ℂ,u=z • Labels.unit su d:=by
       obtain ⟨h,hY⟩:= u.property
       have hv:u.val∈ Labels.localFields su 4:=by
             refine ⟨?_,hY⟩; apply (MvPolynomial.mem_restrictSupport_iff ..).mpr; intro j hj; have he: Labels.height j ≤ d:= (MvPolynomial.mem_restrictSupport_iff ..).mp (show u.val∈Labels.limited su d from h) hj; exact he.trans hd.le
       let p:Labels.Label su 4:=⟨_,hv⟩; obtain ⟨z,g,H⟩:=inputs QCD.simple p
       let Y : GPol:=∑ i:Fin 6,∑ j: Fin 6, g i j • (pairPol su (Extra.WeakScaling.Cube.left i) (Extra.WeakScaling.Cube.right i) (Extra.WeakScaling.Cube.left j) (Extra.WeakScaling.Cube.right j)); -- name
       have hp: u.val=z • (1:GPol)+Y:=by have h:= congr_arg Subtype.val H; simp only[Submodule.coe_add,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul] at h; exact h
       have he:Y∈ Labels.limited su d:=by
             rw[show Y=u.val-z • (1:GPol) from by rw[hp]; abel]; refine Submodule.sub_mem _ h (Submodule.smul_mem _ _ ?_); exact (Labels.unit su d).property.1
       have ht:MvPolynomial.IsWeightedHomogeneous Labels.generation Y 4:=by
            refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun i _=>MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun j _=>?_)); rw [MvPolynomial.smul_eq_C_mul]; apply MvPolynomial.IsWeightedHomogeneous.C_mul; refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun c _=>(pol_bound _ _ c).mul (pol_bound _ _ c))
       have hz:Y=0:=by
            ext i; rw [MvPolynomial.coeff_zero]; by_contra hw; have hs:= ht hw; have hp: Labels.height i≤d:= (MvPolynomial.mem_restrictSupport_iff ..).mp he (MvPolynomial.mem_support_iff.mpr hw); change Labels.height i=4 at hs; omega
       exact ⟨z,Subtype.ext (hp.trans (by rw[hz,add_zero]; rfl))⟩
lemma purse (x:Label d)(hd:d≤8)(S:Submodule ℂ (Label d))(h:∀ u:Labels.Label su (d/2), dowry u∈ S)(he:∀ a b:Flavor 6,∀ i j:Multi d,∀ h:spinWeight i+spinWeight j≤ d,∀ M:Spike, satin a b i j M h∈ S): x∈S:=by
     let I:Finset (Multi d × Multi d):= univ.filter fun i=> spinWeight i.1+spinWeight i.2 ≤ d
     let f(a b:Flavor 6)(i:I):Label d:= satin a b i.val.1 i.val.2 (lamp a b i.val.1 i.val.2 x.val) ((mem_filter.mp i.property).2)
     let Y : Label d:= ∑ a:Flavor 6,∑ b: Flavor 6,∑ i:↥I, f a b i; let g:Labels.Label su (d/2):=⟨fog x.val,sedge x hd⟩; let D:=dowry (d:=d) g
     let W:= x - (D+Y); have ht:W=0:=by
           apply lacks W hd
           · unfold W D Y; simp only [Submodule.coe_sub,Submodule.coe_add,AddSubmonoidClass.coe_finsetSum,_root_.map_sum,map_sub,map_add]; simp only[show fog (dowry (d:=d) g).val=fog x.val from unit_fog _, show ∀ a b i,fog (f a b i).val=0 from fun _ _ _=>fogBA ..,sum_const_zero,add_zero,sub_self]
           intro a b i j ht; unfold W D Y; simp only [Submodule.coe_sub,Submodule.coe_add,AddSubmonoidClass.coe_finsetSum, _root_.map_sum,map_sub,map_add]; rw[show lamp a b i j (dowry (d:=d) g).val=0 from leary ..,zero_add]; simp only[show ∀ a b v, (f a b v).val=bilinear a b (lamp a b v.val.1 v.val.2 x.val) v.val.1 v.val.2 from fun _ _ _=>rfl,fun c e p q M=> c_bare a b c e i j p q M]
           rw[sum_eq_single a (fun u _ h=> by simp [h.symm]) (by simp), sum_eq_single b (fun v _ h=> by simp[h.symm]) (by simp)]
           let l: ↥I:=⟨(i,j),mem_filter.mpr ⟨mem_univ _,ht⟩⟩; rw [sum_eq_single l]; rw [if_pos ⟨rfl,rfl,rfl,rfl⟩]; exact sub_self _
           · intro k _ hw; rw [if_neg (by rintro ⟨-, -, t,hx⟩; exact hw (Subtype.ext (Prod.ext t.symm hx.symm)))]
           simp
     rw[show x=D+Y from sub_eq_zero.mp ht]; exact S.add_mem (h _) (S.sum_mem (fun a _=> S.sum_mem (fun b _=> S.sum_mem (fun i _=> he ..))))
end YM.Sunda
#print axioms YM.Sunda.purse
#print axioms YM.Sunda.unitMine
