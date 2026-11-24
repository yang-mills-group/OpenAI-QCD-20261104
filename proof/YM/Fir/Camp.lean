import YM.Fir.Bells
/-! Full Tag kernel for Label prototypes -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
abbrev TagF:= Σ d:ℕ, Label d
noncomputable abbrev handle (Z:SpaceZ)(t:Fin n→TagF)(x:Points n):ℂ:= Z n (fun i=> (t i).1) x (fun i=> (t i).2)
namespace TagF
lemma feel_eq (Z:SpaceZ) {A B:Fin n→TagF}(h:∀ i,A i=B i)(x:Points n):handle Z A x= handle Z B x:= congr_arg (fun t=>handle Z t x) (funext h)
lemma scope (t: Fin n→TagF) (p:Fin n)(d:ℕ):∃ (D:Fin n→ℕ)(v:(i:Fin n)→ Label (D i)),∃ h:d=D p,∀ u:Label (D p), update t p ⟨d,h.symm ▸ u⟩=fun i:Fin n=> (⟨D i,Function.update v p u i⟩:TagF):=by
    let Z:= update t p ⟨d,(0:Label d)⟩; let D(i):=(Z i).1; let v(i):=(Z i).2; have hz:D p=d:=by unfold D Z; rw[update_self]
    refine ⟨D,v,hz.symm,fun u=>?_⟩; funext i; by_cases h:i=p
    · subst i; rw [update_self,update_self]; exact Sigma.ext hz.symm (by simp ) -- maybe
    rw [update_of_ne h, update_of_ne h]; exact (update_of_ne (α:= Fin n) h _ _).symm -- type
variable (Z:SpaceZ)(x:Points n)(t:Fin n→TagF)(p:Fin n)(d:ℕ)
noncomputable def puts : Label d →ₗ[ℂ]ℂ where
   toFun u:= handle Z (update t p ⟨d,u⟩) x
   map_add' :=by
     obtain ⟨D,v,h,hV⟩:= scope t p d; subst d; intro u w; change handle .. = _; rw [hV (u+w), hV u, hV w]; exact (Z n D x).map_update_add ..
   map_smul' :=by
     obtain ⟨D,v,h,hV⟩:= scope t p d; subst d; intro u w; rw[hV (u•w),hV w]; exact (Z n D x).map_update_smul ..
lemma readsT (p':Fin n→TagF)(hz:∀ i,i≠p →p' i=t i) (d:ℕ)(u:Label d):handle Z (update p' p ⟨d,u⟩) x= puts Z x t p d u:= by
    apply feel_eq; intro i; by_cases h:i=p; subst i; simp; rw [update_of_ne h,update_of_ne h]; exact hz _ h
end TagF
open TagF
namespace Sash
variable (s:Sash G φ)
variable {Z:SpaceZ} (H:Ability P φ Z)
include hp hr hφ H
-- all tags projection to R. identity of kernel on ALL arguments. want EACH slot alone.Out other raw too.
lemma sap (t:Fin n→TagF)(x:Points n)(hx:x∈conf n): handle Z t x = handle Z (fun i=> ⟨(t i).1,s.pointsR (t i).1 none (t i).2⟩) x:=by
    have hi:=(s.guide hp hr hφ H (fun i=>(t i).1) (fun _=>none) (fun i=>(t i).2) x hx); -- order Dot auto
    letI:= alive hp hφ x; exact tendsto_nhds_unique (H.excels n _ x hx (fun i=>(t i).2)) hi
lemma grasp (d:ℕ)(t:Fin n→TagF)(p: Fin n)(u:Label d)(x:Points n)(hx:x∈conf n): puts Z x t p d u=puts Z x t p d (s.pointsR _ none u):=by
    let Q(x:TagF):TagF:= ⟨x.1,s.pointsR x.1 none x.2⟩; let V:= update t p ⟨d,u⟩; let W:=update t p ⟨d,s.pointsR _ none u⟩; have ht:∀ i,Q (V i)= Q (W i):=by
        intro i; by_cases h:i=p; · subst i; unfold V W; rw [update_self,update_self]; have he:= s.rolled hp hr hφ d (s.A none d u); change Sigma.mk d (s.R d (s.A none d u))= Sigma.mk d (s.R d (s.A none d (s.R d (s.A none d u)))); rw [he]
        unfold V W; rw [update_of_ne h,update_of_ne h]
    exact (sap hp hr hφ s H V x hx).trans ((feel_eq Z (A:=fun i=>Q (V i)) (B:=fun i=>Q (W i)) ht x).trans (sap hp hr hφ s H W x hx).symm)
-- all ONE slot representations from Brush price.
-- handle of glass output vs raw.Passage variable p
variable (t: Fin n→TagF)(p:Fin n)
noncomputable abbrev packTag (P:Calibration C)(t:Fin n→TagF)(z:Fin n)(i:ℕ):stalk C i:=stem P (t z).1 i (t z).2

omit hp hr hφ
omit H in
private lemma atTents (t:Fin n→TagF)(D:Fin n→ℕ)(p:Fin n)(w:(i:Fin n)→Label (D i)) (hK:∀ z:Label (D p),update t p ⟨D p,z⟩= fun i=> (⟨D i,update w p z i⟩:TagF)) (v:ℕ→Label (D p))(i:ℕ)(b:Strings n): plain P D i b (update w p (v i))=tube C (packTag P t) p (fun k=>stem P (D p) k (v k)) i b:=by
    change readS C i (fun j=>stem P (D j) i (update w p (v i) j)) b= _; rw [meters]; apply congr_arg (fun u=> readS C i u b); funext j; change stem P (D j) i (update w p (v i) j)=update (fun j=> packTag P t j i) p _ j
    have hq:= hK (v i); by_cases hh:j=p; · subst j; rw [update_self,update_self]
    rw[update_of_ne hh]; have hl:= congr_fun hq j; rw [update_of_ne hh] at hl; change stem P (D j) i (w j)= update (fun j=> packTag P t j i) p _ j; rw [update_of_ne hh]; unfold packTag; rw[hl]; change _= stem P _ _ (update w p (v i) j); rw[update_of_ne hh]
set_option maxHeartbeats 380000 in
lemma orient {d:ℕ}(v:ℕ→Label d)(z:Label d)(h:Tendsto (v ∘ φ) atTop (𝓝 z))(x:Points n)(hx:x∈conf n):Exposes C φ (fun i=> tube C (packTag P t) p (fun k=>stem P d k (v k)) (φ i)) x (puts Z x t p d z) :=by
    obtain ⟨D,w,he,hK⟩:= TagF.scope t p d; subst d; let W(k):=(update w p k)
    have hW:Tendsto (fun i=>W (v (φ i))) atTop (𝓝 (W z)):=tendsto_pi_nhds.mpr fun j=> by
         by_cases he:j=p; · subst j; unfold W; simp only [update_self]; exact h
         unfold W; simp only [update_of_ne he]; exact tendsto_const_nhds
    have hV:= Ability.turns D (W z) H (fun i=>W (v (φ i))) hW x hx; have he:puts Z x t p (D p) z=Z n D x (W z):=by
        change handle Z (update t p ⟨D p,z⟩) x= _; rw[hK z]
    rw [he]; exact hV.congr (fun i=> atTents t D p w hK v (φ i.1) i.2)
end Sash
end YM.Massive.Fir
#print axioms YM.Massive.Fir.Sash.grasp
#print axioms YM.Massive.Fir.Sash.orient
#print axioms YM.Massive.Fir.TagF.puts
