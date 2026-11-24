import YM.Tarn.Rays
/-! Intrinsic action descended from all correlated primaries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} (hQ:P.System) {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q:Choir}(h:Q.Domestic)
namespace Domestic
include h
lemma tidal (v:Q.W)(u:Averaging):∃ d,∃ p:Label d,Q.focus u d p=v:=by obtain ⟨d,hv⟩:=h.absorbs v; exact ⟨d,show v∈ LinearMap.range (Q.focus u d) from h.tops u d|>.symm ▸ hv⟩
lemma braces (v w:Q.W)(u:Averaging):∃ d,∃ p q:Label d,Q.focus u d p=v∧ Q.focus u d q=w:=by
    obtain ⟨i,hi⟩:= h.absorbs v; obtain ⟨j,hj⟩:= h.absorbs w; let d:=max i j; obtain ⟨p,hp⟩:=(show v∈LinearMap.range (Q.focus u d) from h.tops u d|>.symm ▸ (h.slope (le_max_left ..) hi)); obtain ⟨q,hq⟩:=(show w∈LinearMap.range (Q.focus u d) from h.tops u d|>.symm ▸ (h.slope (le_max_right ..) hj)); exact ⟨d,p,q,hp,hq⟩
lemma same (x y:Q.W)(H:∀ (u:Points 2),u∈conf 2→∀ z:Q.W,Q.total 2 u ![z,x]=Q.total 2 u ![z,y]):x=y:= by
     by_contra he; obtain ⟨u,hp,z,hZ⟩:= h.listens (x-y) (sub_ne_zero.mpr he); let U:=points ![0,u]; apply hZ; have he:u≠0:=fun hv=>by have h:=hp timeAxis; rw [hv] at h; exact lt_irrefl _ h
     have hx:U∈conf 2:=by intro i j hx; by_contra hi; fin_cases i<;> fin_cases j<;> first|contradiction| exact he hx| exact he hx.symm
     let F:=Q.total 2 U; have hh(v:Q.W): ![z,v]=Function.update (![z,x]) 1 v:= by ext1 i; fin_cases i <;> rfl
     change F ![_,_]=_; rw [hh,F.map_update_sub,←hh,←hh,H U hx,sub_self]
variable {σ:ℂ→+*ℂ}
lemma crown (M:∀ d,Label d→ₛₗ[σ]Label d)(G:Averaging→ Averaging)(J:∀ d e u w p q, Q.focus u d p=Q.focus w e q→Q.focus (G u) d (M d p)=Q.focus (G w) e (M e q)): ∃ Z: Q.W→ₛₗ[σ] Q.W,∀ u d v,Z (Q.focus u d v)= Q.focus (G u) d (M d v) :=by
     choose d p hp using fun v=> h.tidal v none; let F(v:Q.W):= Q.focus (G none) (d v) (M _ (p v)); have H(u d v): F (Q.focus u d v)= Q.focus (G u) d (M d v):= J _ _ none _ _ _ (hp _)
     let T: Q.W→ₛₗ[σ] Q.W:= {
        toFun:=F
        map_add':=fun v z=> by
            obtain ⟨d,p,q,hp,hq⟩:= h.braces v z none; rw[←hp,←hq,← map_add,H,H,H,map_add,map_add]
        map_smul':=fun c x=>by
            obtain ⟨d,p,hp⟩:=h.tidal x none; rw [←hp,←map_smul,H,H,map_smulₛₗ,map_smul] }
     exact ⟨T,H⟩
-- general 2-place oriented slot result.Brace first oriented perm reverse implicitly.
abbrev Ticket:= Σ d:ℕ, Label d × Averaging
noncomputable abbrev moor (Q:Choir)(t:Ticket):=Q.focus t.2.2 t.1 t.2.1
noncomputable abbrev shiftT (M:(d:ℕ)→ Label d→Label d)(G:Averaging→Averaging)(t:Ticket):Ticket:=⟨t.1,M _ t.2.1,t.2.2|> G⟩
lemma counterparts (M:(d:ℕ)→Label d→Label d)(hM:∀ i,Surjective (M i))(G:Averaging→Averaging) (ρ:Equiv.Perm (Fin 2))(τ:Points 2→Points 2)(hv:∀ x∈conf 2,∃ y∈conf 2,τ y=x)(k:ℂ→ ℂ)(hk:∀ x∈conf 2,∀ g:Fin 2→ Ticket,Q.total 2 (τ x) (moor Q∘shiftT M G ∘ g ∘ρ)= k (Q.total 2 x (moor Q ∘g))) :∀ u v, moor Q u=moor Q v→moor Q (shiftT M G u)=moor Q (shiftT M G v):=by
     intro u v hq; apply h.same; intro y hy z; obtain ⟨x,hx,rfl⟩:=hv y hy; obtain ⟨i,w,hw⟩:=h.tidal z (G none); obtain ⟨l,rfl⟩:=hM i w; let U:Ticket:=⟨i,l,none⟩; let F(v:Ticket):Fin 2→Ticket:=(![U,v]) ∘ρ.symm
     have he(v:Ticket) : moor Q∘shiftT M G ∘ F v ∘ρ=![z,moor Q (shiftT M G v)] :=by
          funext i; simp only [Function.comp_apply,F, Equiv.symm_apply_apply]; fin_cases i; exact hw; rfl
     have hf: moor Q ∘ F u= moor Q ∘ F v:=by funext i; obtain ⟨j,rfl⟩:=ρ.surjective i; simp only[comp_apply,F,Equiv.symm_apply_apply]; fin_cases j; rfl; exact hq
     rw [←he,←he,hk _ hx,hk _ hx,hf]
end Domestic
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Domestic.crown
#print axioms YM.Massive.Tarn.Choir.Domestic.counterparts
