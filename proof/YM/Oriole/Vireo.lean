import YM.Tinus.Cents
import YM.Massive.Hawser.Temple
import YM.QCD.Stew.Silver
import YM.Massive.PCAC.Smalt
/-! Colored form coordinate system. UV.Label count in a full money lane.
`jcoat D` = positive P sign (i.e. `- Grass.form D`). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
abbrev CensusA (d:ℕ):=Matrix (SpinMode d) (SpinMode d) ℂ
section
variable {A:Type*}[Fintype A]
open Finset Grass.Ward
noncomputable def coat : Matrix A A ℂ→ₗ[ℂ]Dirac A := { toFun:=fun x=> - form x, map_add':=fun x y=> by simp only [form_add,neg_add],map_smul':=fun c x=>by simp only [form,smul_neg, smul_sum,Matrix.smul_apply,smul_smul,smul_eq_mul]; rfl }
noncomputable def uncoat : Dirac A→ₗ[ℂ] Matrix A A ℂ:= { toFun:=fun x=> - traceP x,map_add':=fun x y=>by ext i j; change - -_= _; simp [traceP], map_smul':=fun c x=>by ext i j; simp [traceP] }
lemma coat_known (D: Matrix A A ℂ): uncoat (coat D)=D:=by
     change uncoat (- form D)=_; rw [map_neg]; ext i j; change - - -coef _ (vary (.inl j) (vary (.inr i) (form D)))=_; rw [form_row,map_neg,map_sum]; simp_rw [map_smul,psi,vary_atom]; have hp:coef (∅:Finset (Pairs A)) (1:Dirac A)=1:=by rw [← mono_empty]; exact read ∅;
     simp [hp,probe,Pi.single_apply,mul_ite]
end
open Poised.Display Poised.Stative Module Finset
local notation "W"=>CensusA d
noncomputable def jcoat : W→ₗ[ℂ] Pol d:=((TensorProduct.mk ℂ GPol _) 1).comp coat
noncomputable def juncoat : Pol d→ₗ[ℂ] W:= uncoat.comp (ready d 0)
lemma j_coat (x:W): juncoat (jcoat x)=x:=by unfold juncoat jcoat; rw [LinearMap.comp_apply,LinearMap.comp_apply,TensorProduct.mk_apply,ready_t,map_one,one_smul,coat_known]
lemma inj_coat : Injective (jcoat (d:=d)):=Function.LeftInverse.injective j_coat
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
lemma bladeX {B:Type*}[Fintype B][DecidableEq B](x y:B)(h:x≠y): atom x*atom y=mono {x,y} ∨ atom x*atom y= -mono {x,y}:=by
     have he:Disjoint ({x}:Finset B) {y}:=by simp[h]
     let H:=Finset.disjUnion ({x}:Finset B) {y} he; have hH:H={x,y}:=by unfold H; simp
     have h0 := mono_mul_sign {x} {y} he; rw [show Finset.disjUnion _ _ he= {x,y} from hH,mono_single,mono_single] at h0; exact h0
lemma buck(u:FlavorTorus)(i:Ae) : adapter (byFlavor u fun i:T=>i.2) (byFlavor u⁻¹ fun i:T=>i.2) (atom i)=(Sum.elim (fun i:T=>(u i.2).val) (fun i:T=>star (u i.2).val) i) • atom i:=by
      rcases i with i|i
      · rw [show atom (Sum.inl i)=psi i from rfl, adapt_psi]; simp [byFlavor,Matrix.diagonal_apply,ite_smul] -- infer
      rw [show atom (Sum.inr i)=bar i from rfl, adapt_bar]; simp [byFlavor,Matrix.diagonal_apply,ite_smul]; rfl
noncomputable def ic (a:Flavor 6): FlavorTorus := fun i=> if i=a then ⟨Complex.I,⟨by simp,by simp⟩⟩ else 1
-- all words in OffSym range `i=head bar, j=head col`
def warmth (a b:Flavor 6)(p:PowerPair d) :Prop := ∃ i j:T,i.2=a ∧ j.2=b ∧ p=(0,{.inr i,.inl j})
variable (x:Label d)
noncomputable def CharmC (a b:Flavor 6)(x:Pol d) := ∀ v:FlavorTorus,flavorAct v x= paidM a b v • x
section
variable (h:a≠b)(hx:CharmC a b x.val)
include h hx
lemma paired (hd:d≤8)(j:Rings d)(hv:coord j.val x.val≠0): warmth a b j.val:=by
    have hT(p:Flavor 6)(hp:p=a∨p=b): flavorAct (ribbonK p) x.val= -x.val:=by
            rw [hx]; unfold paidM PCAC.ribbonK PCAC.bandK; cases hp with | inl hz=> subst p; simp [h.symm]; exact neg_one_smul ℂ x.val | inr hz=> subst p; simp [h]; exact neg_one_smul ℂ x.val
    obtain ⟨u,hu,hau⟩:=darkens x a (hT _ (Or.inl rfl)) j hv; obtain ⟨v,hv',hbv⟩:=darkens x b (hT _ (.inr rfl)) j hv
    have he:u≠v:=by intro q; exact h (hau.symm.trans (q ▸ hbv))
    have hb: UV.weight j.val ≤ 8 := ((Set.Finite.mem_toFinset (weightFinite d)).mp j.property : weight j.val ≤ d) |>.trans hd
    let k:= j.val.1; let t:=j.val.2; have hm:= le_trans (show 2*Labels.height k+(∑ i∈t,letterWeight i) ≤ 8 from hb) le_rfl
    have hx':#t*3≤ ∑ i∈t, letterWeight i:=by rw [show #t*3=∑ _i∈t,(3:ℕ) from (by simp)]; exact sum_le_sum fun i _=> Nat.le_add_right ..
    have hp':({u,v}:Finset Ae)⊆t:=Finset.insert_subset hu (singleton_subset_iff.mpr hv'); have hC:=card_pair he; have hf: #t ≤ 2:=by omega
    have hT:t={u,v}:=(eq_of_subset_of_card_le hp' (hf.trans_eq hC.symm)).symm
    have ht:k=0:=by
         by_contra hP; obtain ⟨i,hi⟩:= Finsupp.support_nonempty_iff.mpr hP; have h:2 ≤ Labels.height k:=by
             unfold Labels.height; have hp:= single_le_sum (f:=fun i:Labels.Key su=> k i • Labels.generation i) (fun a _=> Nat.zero_le _) hi; change 2 ≤ ∑ i∈k.support, k i • Labels.generation i
             exact le_trans (b:=k i • Labels.generation i) (le_trans (Nat.le_add_left 2 i.1) (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)))) hp
         rw [hT,hC] at hx'; rw [hT] at hm; omega -- rhs t in hx' rewrites
    have hP:j.val=(0,{u,v}):= Prod.ext ht hT
    let Q(z:FlavorTorus):=Sum.elim (fun i:T=>(z i.2).val) (fun i:T=>star (z i.2).val)
    -- exploit diagonal flavor
    have hL(P:PowerPair d)(w:FlavorTorus) : ∃ c:ℂ, flavorAct w (gen P)=c • gen P:=by -- need analog wscale complex
          unfold gen flavorAct; rw [TensorProduct.map_tmul]; let p:=P.2; suffices H: ∃ c:ℂ, adapter (byFlavor w fun i:T=>i.2) (byFlavor w⁻¹ fun i:T=>i.2) (mono p)=c • mono p by
               obtain ⟨c,h⟩:=H; refine ⟨c,?_⟩; rw [← tmul_smul]; exact congr_arg₂ (tmul ℂ) rfl h
          let Y:= adapter (byFlavor w fun i:T=>i.2) (byFlavor w⁻¹ fun i:T=>i.2); obtain ⟨f,-,-,hQ⟩:= expression p
          have h(Z:List Ae) : ∃ c:ℂ,Y (Z.map atom).prod=c • (Z.map atom).prod:=by
               induction Z with
               | nil=> exact ⟨1,by simp⟩
               | cons i l ih=> obtain ⟨c,h⟩:=ih; refine ⟨Q w i*c,?_⟩; simp only [List.map_cons,List.prod_cons]; rw [map_mul,h,show Y (atom i)=_ from buck w i,mul_smul]; rw [smul_mul_assoc, mul_smul_comm]
          rw [hQ]; simpa only [List.map_ofFn] using h (List.ofFn f)
    have he'(w:FlavorTorus) : Q w u*Q w v= paidM a b w:=by
          let σ:=Q w u*Q w v
          have he1: flavorAct w (gen j.val)=σ • gen j.val:=by
                  rw [hP,flavorAct,gen,TensorProduct.map_tmul, ← TensorProduct.tmul_smul]; congr 1
                  simp only [AlgHom.toLinearMap_apply]; rcases bladeX u v he with hz|hz
                  · rw [← hz,map_mul,buck,buck,smul_mul_assoc,mul_smul_comm,show σ =Q w u*Q w v from rfl,mul_smul] -- show implicit inspect
                  rw [show mono ({u,v}:Finset Ae)= -(atom u*atom v) from by rw [hz,neg_neg],map_neg,map_mul,buck,buck,smul_neg,smul_mul_assoc, mul_smul_comm]; congr 1; rw [show σ =Q w u*Q w v from rfl,mul_smul] -- orientation eq name
          have hu:(coord j.val).comp (flavorAct w)=σ • coord j.val:=by
                  apply (zBasis d).ext; intro i; rw [LinearMap.comp_apply,minted]; by_cases h:j.val=i
                  · subst i; rw [he1,map_smul]; rfl
                  obtain ⟨c,hP⟩:= hL i w; rw [hP,map_smul, LinearMap.smul_apply,show coord j.val (gen i)=0 from ?_,smul_zero,smul_zero]; rw [coord,← minted]; simp [h]
          apply mul_right_cancel₀ hv; exact (LinearMap.congr_fun hu x.val).symm.trans (by rw [LinearMap.comp_apply,hx,map_smul]; rfl)
    have h1:= he' (ic a); have h2:= he' (ic b); have hr:Complex.I ≠ -Complex.I:=by intro h; exact Complex.I_ne_zero (neg_eq_self.mp h.symm)
    rcases u with u|u<;>rcases v with v|v
    all_goals change _ =_ at hau hbv; simp only [Sum.elim_inl,Sum.elim_inr] at hau hbv
    · simp [Q,hau,hbv,paidM,h,h.symm,ic] at h1; exact False.elim (hr h1)
    · simp [Q,hau,hbv,paidM,h,h.symm,ic] at h1; exact False.elim (hr h1)
    · exact ⟨u,v,hau,hbv,hP⟩
    · simp [Q,hau,hbv,paidM,h,h.symm,ic] at h2; exact False.elim (hr h2.symm)
end
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.paired
