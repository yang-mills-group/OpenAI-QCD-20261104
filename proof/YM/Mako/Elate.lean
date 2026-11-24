import YM.Mako.Iker
set_option maxHeartbeats 580000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis×Axis→ K.W}
variable {A:Axle K (fun a b=>W (a,b))}(HK:K.Domestic)(R:Roof P.sym)
structure Steps {A:Axle K (fun a b=>W (a,b))} (T:Pollens P K)(R:Roof P.sym) (p:EuPin →* (K.W ≃ₗ[ℂ] K.W)) :Prop where
    tones(d:ℕ)(hd:8≤d)(F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d))(hF: Flyers A d hd T F)(t:EuPin)(x:Free.Symbol d): p t (F x).val = (F (caravan R d t x)).val
variable (h:∀ (d:ℕ) (hd:8 ≤ d), ∃ (F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d)), Flyers A d hd T F)
include h HK
lemma attains(p:EuPin):∃ L: Module.End ℂ K.W,∀ d :ℕ, ∀ hd:8 ≤d,∀ F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d), Flyers A d hd T F→ ∀ v:Free.Symbol d,L (F v)= (F (caravan R d p v)).val:=by
     choose u hu using h
     let F(d):Free.Symbol (8+d)≃ₗ[ℂ] ↥(K.level (8+d)):=u (8+d) (Nat.le_add_right ..)
     choose j hj using HK.absorbs
     let B(x:K.W):= (F (j x)).symm (⟨x,HK.slope (Nat.le_add_left ..) (hj x)⟩ :K.level (8+j x))
     let Q(x:K.W):= (F (j x) (caravan R (8+j x) p (B x))).val
     have hx(x:K.W): (F (j x) (B x)).val=x:=congr_arg Subtype.val ((F _).apply_symm_apply _)
     have hz(d:ℕ)(hd:8≤d)(Y:Free.Symbol d≃ₗ[ℂ]↥(K.level d))(hf:Flyers A d hd T Y)(v:Free.Symbol d): Q (Y v).val= (Y (caravan R d p v)).val:=by
           let X:= (Y v).val; let i:= max (8+j X) d; have hv: 8+j X≤ i:=le_max_left ..; have he: d≤ i:=le_max_right ..; let Z:=u i (hd.trans he)
           let t: Free.Symbol i:= Z.symm ⟨X,HK.slope he (Y v).property⟩; have ht: (Y (caravan R d p v)).val= (Z (caravan R i p t)).val:= (YM.Mako.tones HK R hd Y hf Z _ (hu _ _) he p v).symm
           have hh:= tones HK R (Nat.le_add_right 8 (j X)) (F (j X)) (hu _ _) Z _ (hu _ _) hv p (B X)
           have hy: Z.symm (⟨(F _ (B X)).val,HK.slope hv (F _ (B X)).property⟩:K.level i)= t:= congr_arg _ (Subtype.ext (hx X)); rw[ht,←hy]; exact hh.symm
     refine ⟨{toFun:=Q,map_add':= ?_,map_smul':=?_},hz⟩
     · intro x y; let i:=max (j x) (j y); let v x (hx:j x≤ i):= (F i).symm ⟨x,HK.slope (hx.trans (Nat.le_add_left ..)) (hj x)⟩; let a:=v x (le_max_left ..); let b:=v y (le_max_right ..); have hx₀:(F i a).val=x:=congr_arg Subtype.val ((F i).apply_symm_apply _); have hx₁:(F i b).val=y:=congr_arg Subtype.val ((F i).apply_symm_apply _)
       rw[← hx₀,←hx₁,← Submodule.coe_add,←map_add,hz _ _ (F _) (hu _ _),hz _ _ (F _) (hu _ _),hz _ _ (F _) (hu _ _),map_add,map_add,Submodule.coe_add]
     intro r x; let z:=B x; let m:= j x; let Y:=F m; have hE : (Y z).val=x:= hx _; rw [show r • x=(Y (r • z)).val from ?_,hz _ _ Y (hu _ _),show Q x=(Y (caravan R (8+m) p z)).val from rfl,map_smul,map_smul]; rfl
     rw[map_smul,Submodule.coe_smul,hE]
lemma edict:∃ p:EuPin →* (K.W≃ₗ[ℂ]K.W), Steps (A:=A) T R p:=by
     choose u hu using attains HK R h
     have spreads(v:K.W):∃ d:ℕ,∃ hd:8 ≤d,v∈K.level d:=by obtain ⟨d,hd⟩:= HK.absorbs v; exact ⟨8+d,Nat.le_add_right .., HK.slope (Nat.le_add_left ..) hd⟩
     have hM(p q:EuPin)(x:K.W): u (p*q) x=u p (u q x):=by
           obtain ⟨i,hi,hx⟩:=spreads x; obtain ⟨F,hF⟩:= h _ hi; obtain ⟨v,hv⟩:=F.surjective ⟨x,hx⟩; have he:(F v).val=x:= congr_arg Subtype.val hv; rw[←he,hu _ _ _ F hF,hu _ _ _ F hF,hu _ _ _ F hF,map_mul]; rfl
     have hN(x:K.W): u 1 x=x:=by
           obtain ⟨i,hi,hx⟩:=spreads x; obtain ⟨F,hF⟩:= h _ hi; obtain ⟨v,hv⟩:=F.surjective ⟨x,hx⟩; have he:(F v).val=x:=congr_arg Subtype.val hv; rw[←he,hu _ _ _ F hF,map_one]; rfl
     let v(p:EuPin):K.W≃ₗ[ℂ]K.W:=
        { u p with invFun:= u p⁻¹
                   left_inv:=fun x=>by change u p⁻¹ (u p x)= _; rw[←hM,inv_mul_cancel,hN]
                   right_inv:=fun x=>by change u p (u p⁻¹ x)=_; rw[←hM,mul_inv_cancel,hN] }
     exact ⟨⟨⟨v,LinearEquiv.ext hN⟩,fun p q=>LinearEquiv.ext (hM p q)⟩,⟨fun d hd F hF p=> hu p d hd F hF⟩⟩
end YM.Mako
#print axioms YM.Mako.edict
