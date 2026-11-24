import YM.Plateau.Curio
import YM.Oriole.Gay
/-! Flavor parity at d≤10. Keep both Lorentz sorts independent on each flavor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
variable (x:Label d)
def Quiet (p:Pol d):Prop:= parityAct p=p ∧ ∀ u:FlavorTorus, flavorAct u p=p
variable (j:Rings d)
local notation "c"=>j.val
lemma judge (hv:coord j.val x.val≠0)(S:Pol d→ₗ[ℂ]Pol d)(hp:∀ i:PowerPair d,∃ t:ℂ,S (gen i)= t • gen i) (hx:S x.val=x.val)(r:ℂ)(hr:S (gen j.val)= r • gen j.val):r=1:=by
     have hu : (coord j.val).comp S=r • coord j.val:=by
                  apply (zBasis d).ext; intro i; rw [LinearMap.comp_apply,minted]; by_cases h:j.val=i
                  · subst i; rw [hr,map_smul]; rfl
                  obtain ⟨q,hP⟩:= hp i; rw [hP,map_smul, LinearMap.smul_apply,show coord j.val (gen i)=0 from ?_,smul_zero,smul_zero]; rw [coord,← minted]; simp [h]
     apply mul_right_cancel₀ hv; exact (LinearMap.congr_fun hu x.val).symm.trans (by rw[LinearMap.comp_apply,hx,one_mul])
noncomputable abbrev charon (z:FlavorTorus) : Ae→ℂ:= Sum.elim (fun i:T=>(z i.2).val) (fun i:T=>star (z i.2).val)
lemma flavor_scalar (P:PowerPair d)(w:FlavorTorus) : ∃ z:ℂ, flavorAct w (gen P)=z • gen P:=by -- analogous wscale complex
          unfold gen flavorAct; rw [TensorProduct.map_tmul]; let p:=P.2; suffices H: ∃ z:ℂ, adapter (byFlavor w fun i:T=>i.2) (byFlavor w⁻¹ fun i:T=>i.2) (mono p)=z • mono p by
               obtain ⟨e,h⟩:=H; refine ⟨e,?_⟩; rw [← tmul_smul]; exact congr_arg₂ (tmul ℂ) rfl h
          let Y:= adapter (byFlavor w fun i:T=>i.2) (byFlavor w⁻¹ fun i:T=>i.2); obtain ⟨f,-,-,hQ⟩:= expression p
          have h(Z:List Ae) : ∃ z:ℂ,Y (Z.map atom).prod=z • (Z.map atom).prod:=by
               induction Z with
               | nil=> exact ⟨1,by simp⟩
               | cons i l ih=> obtain ⟨t,h⟩:=ih; refine ⟨charon w i*t,?_⟩; simp only [List.map_cons,List.prod_cons]; rw [map_mul,h,show Y (atom i)=_ from buck w i,mul_smul]; rw [smul_mul_assoc, mul_smul_comm]
          rw [hQ]; simpa only [List.map_ofFn] using h (List.ofFn f)
lemma orderR (h:Quiet x.val)(hd:d≤10)(hp:coord j.val x.val≠0): j.val.2=∅∨∃ i k:T,i.2=k.2 ∧ j.val.2={.inr i,.inl k}:=by
    let k:= j.val.1; let t:=j.val.2; have hx': #t*3 ≤ ∑ i∈t,letterWeight i:=by rw [show #t*3=∑ _i∈t,(3:ℕ) from (by simp)]; exact sum_le_sum fun i _=> Nat.le_add_right ..
    have hQ:2*Labels.height k+∑ i ∈t,letterWeight i ≤ 10:= ((Set.Finite.mem_toFinset (weightFinite d)).mp j.property : weight j.val ≤ d) |>.trans hd
    have he(i:PowerPair d): parityAct (gen i)=(-1:ℂ)^ #i.2 • gen i:=by unfold gen parityAct; rw [TensorProduct.map_tmul,AlgHom.toLinearMap_apply,Grass.grade_mono, TensorProduct.tmul_smul]; rfl
    have hT : (-1:ℂ)^ #t=1:= judge x j hp parityAct (fun i=>⟨_,he i⟩) h.1 _ (he _)
    have hu:#t=0∨ #t=2:=by rcases (show #t=0∨ #t=1∨ #t=2∨ #t=3 from by omega) with h0|h0|h0|h0; left; exact h0; norm_num[h0] at hT; right; exact h0; norm_num[h0] at hT
    rcases hu with h0|h0; · left; exact card_eq_zero.mp h0
    right; obtain ⟨u,v,hv,H⟩:=Finset.card_eq_two.mp h0
    have ec (w:FlavorTorus): charon w u*charon w v=1:=by
         apply judge x j hp (flavorAct w) (fun P=>flavor_scalar P w) (h.2 w)
         have hP:j.val=(k,{u,v}):= Prod.ext rfl H; rw [hP,flavorAct,gen,TensorProduct.map_tmul,← TensorProduct.tmul_smul]; congr 1
         simp only [AlgHom.toLinearMap_apply]; rcases bladeX u v hv with hz|hz
         · rw [← hz,map_mul,buck,buck,smul_mul_assoc,mul_smul_comm,mul_smul] -- mul_smul confusion
         rw [show mono ({u,v}:Finset Ae)= -(atom u*atom v) from by rw [hz,neg_neg],map_neg,map_mul,buck,buck,smul_neg,smul_mul_assoc, mul_smul_comm,mul_smul]
    change j.val.2={u,v} at H; rw [H]; rcases u with u|u<;>rcases v with v|v
    · have hz:=ec (ic u.2); by_cases h:v.2=u.2 <;> simp[ic,h,charon,Complex.ext_iff] at hz <;> norm_num at hz
    · refine ⟨v,u,?_,Finset.pair_comm ..⟩; by_contra h; have hz:=ec (ic v.2); simp[ic,Ne.symm h,charon,Complex.ext_iff] at hz
    · refine ⟨u,v,?_,rfl⟩; by_contra h; have hz:=ec (ic u.2); simp[ic,Ne.symm h,charon,Complex.ext_iff] at hz
    have hz:=ec (ic u.2); by_cases h:v.2=u.2 <;> simp[ic,h,charon,Complex.ext_iff] at hz <;> norm_num at hz
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.orderR
