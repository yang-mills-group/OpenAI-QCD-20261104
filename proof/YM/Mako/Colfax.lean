import YM.Mako.Flight
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Module
open scoped Topology BigOperators Classical
variable {W V:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W][AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V]
variable {C:Set (End ℂ W)}{D: End ℂ W}
variable {σ:ℂ→+*ℂ}[RingHomInvPair σ σ]
variable (f: W ≃ₛₗ[σ] W)
lemma shack (s:Split D C)(h:∀ i∈C,∃ j∈C,∀ v:W,f (i v)= j (f v))(H:∀ j∈ C,∃ i∈C,∀ v:W,f (i v)=j (f v))(v:W): D (f v)= f (D v):=by
     have ht:D (f (D v))= f (D v):=by
           apply s.budget.identity; intro i hi; obtain ⟨j,hj,he⟩:= H i hi; rw [←he,← Module.End.mul_apply,s.hit j hj, LinearMap.zero_apply,map_zero]
     let U:= LinearMap.ker (D.comp f.toLinearMap); have hp(i:End ℂ W)(hi:i∈C)(y:W):i y∈U:=by
           obtain ⟨j,hj,hg⟩:=h i hi; show D (f (i y))= 0; rw[hg,←Module.End.mul_apply,s.gun j hj]; rfl
     have hv: D (f (D v - v))=0:= s.budget.hits U v hp; rw [map_sub,map_sub,ht,sub_eq_zero] at hv; exact hv.symm
local notation "M"=> W→ₗ[ℂ]V
variable (g:V ≃ₛₗ[σ]V)
-- product representation on Hom
noncomputable def viewδ : (W→ₗ[ℂ] V) →ₛₗ[σ] (W→ₗ[ℂ] V):=
    { toFun:=fun p=> LinearMap.comp (g.toLinearMap) (p.comp f.symm.toLinearMap)
      map_add':=fun p q=>by ext1 x; simp [map_add]
      map_smul':=fun s v=>by ext1 x; simp [map_smulₛₗ] }
@[simp]lemma vis (x:W)(p:M): viewδ f g p x= g (p (f.symm x)):=rfl
noncomputable def windP: (W→ₗ[ℂ]V)≃ₛₗ[σ] (W→ₗ[ℂ] V):=
    { viewδ f g with
      invFun:=viewδ f.symm g.symm
      left_inv:=fun x=>by refine LinearMap.ext fun i=>?_ ; change viewδ _ _ (viewδ _ _ x) i=x i; simp
      right_inv:=fun x=> by refine LinearMap.ext fun i=>?_ ; change viewδ _ _ (viewδ _ _ x) i=x i; simp }
lemma cowind(p q:End ℂ W)(P Q:End ℂ V)(h:∀ i,f (p i)= q (f i))(H:∀ i,g (P i)=Q (g i))(v:M): windP f g (power p P v)=power q Q (windP f g v):=by
     ext1 i; obtain ⟨i,rfl⟩:= f.surjective i; change viewδ f g (power p P v) (f i)= power q Q (viewδ f g v) (f i); rw [vis,power_app,power_app,map_sub,H,vis,vis,←h,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply] -- last? inspect
lemma shoes (p:M): windP f g p=p ↔ ∀ i:W,p (f i)=g (p i):=by
     constructor
     · intro h i; have ht:=DFunLike.congr_fun h (f i); change g (p (f.symm (f i)))=_ at ht; rw[LinearEquiv.symm_apply_apply] at ht; exact ht.symm
     intro h; ext1 i; change g (p (f.symm i))=_; rw[←h,LinearEquiv.apply_symm_apply]
variable {ι:Type*}(p:ι→ End ℂ W)(P:ι→End ℂ V)(t:ι→ι)(ht:Surjective t)
include ht
lemma weft (hz:∀ i j,f (p i j)=p (t i) (f j))(hQ:∀ i j,g (P i j)=P (t i) (g j)) (F:M)(Df:End ℂ M)(h:Split Df (range fun i=> power (p i) (P i))) (hF:∀ i,F (f i)=g (F i)) (x:W): (Df F) (f x)=g ((Df F) x):=by
       apply (shoes f g _).mp _ x; let V':=windP f g; change V' (Df F)=_; rw [←shack V' h _ _ F,(shoes f g F).mpr hF]
       · rintro i ⟨y,rfl⟩; exact ⟨_,⟨t y,rfl⟩,cowind f g _ _ _ _ (hz y) (hQ y)⟩
       rintro q ⟨y,rfl⟩; obtain ⟨i,rfl⟩:= ht y; exact ⟨_,⟨i,rfl⟩, cowind f g _ _ _ _ (hz i) (hQ i)⟩
-- special unit: eval Lie operators kills. if on F,F carries unit; all generators kill at v. 
end YM.Mako
#print axioms YM.Mako.weft
