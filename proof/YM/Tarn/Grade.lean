import YM.Tarn.Word
/-! Graded fields exact receipts in real ensemble. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set TensorProduct HarmonyF Strip
open Poised Poised.Plans Poised.Plans.Stamp QCD.Grass Needle
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q: Choir} {φ:ℕ→ℕ}(h:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)(hQ:P.System)
variable (L:Pollens P Q)
abbrev markedW (p:Bool)(w:Q.W):= L.parity w= if p then -w else w
namespace Petals
include h
variable {p:Bool} {u:Averaging}
lemma tickets {v:Q.W}(u:Averaging)(hq:markedW L p v):∃ d,∃ x:Label d, Q.focus u d x=v ∧ P.sym.parity d x= if p then -x else x:=by
    obtain ⟨d,x,hx⟩:= h.h.tidal v u; let f:=Q.focus u d; let y:= facing P.sym p x; refine ⟨d,y,?_,?_⟩
    · have ht: f (P.sym.parity d x)=(if p then -v else v):= (L.p d u x).symm.trans ((congr_arg L.parity hx).trans hq); change f y=v; cases p <;> simp only [facing,y,Bool.false_eq_true,↓reduceIte,map_smul,map_sub,map_add] <;> rw [show f x= _ from hx, ht] <;> simp only [Bool.false_eq_true,↓reduceIte, sub_neg_eq_add] <;> rw [←two_smul ℂ,smul_smul, inv_mul_cancel₀ (by norm_num),one_smul]
    apply Subtype.ext; have H:= fronting P.sym x p -- order check
    rw [RawSym.parityActs]; cases p
    · change UV.parityAct y.val=y.val; exact H.trans (one_smul ℂ _) -- expects trans because defeq?
    change UV.parityAct y.val= -y.val; refine H.trans ?_; rw [show gammaQ true= -1 from rfl, ← show (facing P.sym true x).val=y.val from rfl]; exact neg_one_smul ℂ y.val
abbrev Atlas (C:Sequence)(P:Calibration C)(φ:ℕ→ℕ)(x: Petal P):Prop:= Tendsto (fun k=> digit (C.S.spacing (C.N (φ k))) (x.r k)) atTop (𝓝 x.x)
abbrev sight(u:Averaging)(Q:Choir)(x:Petal P):= (x.x,lap Q u x.fieldT)
noncomputable abbrev planted (P:Calibration C) (V: E4) (φ:ℕ→ℕ)(v:TagF):Petal P:=⟨v,fun i=> bead (C.S.spacing (C.N (φ i))) V,V⟩
omit h in
include hp hφ in
lemma aliveP (V:E4)(t:TagF):Atlas C P φ (planted P V φ t):= (approaches hp V).comp hφ
include hp hφ
lemma seeks (l:Strip Q)(u:Averaging):∃ p:List (Petal P),petals Q u p=l ∧∀ z∈p, Atlas C P φ z:=by
    induction l with
    | nil=>exact ⟨[],rfl,by simp⟩
    | cons a l ih=>
         obtain ⟨p,H,hp'⟩:= ih; obtain ⟨d,g,hg⟩:=h.h.tidal a.2 u; let z:=planted P a.1 φ ⟨d,g⟩; refine ⟨z::p,List.cons.injEq .. |>.mpr ?_,?_⟩
         · exact ⟨Prod.ext rfl hg,H⟩
         intro v hv; rcases List.mem_cons.mp hv with e|e; exact e ▸ aliveP hp hφ _ _; exact hp' _ e
omit h hp hφ
include hQ hφ
lemma acted (z:Petal P)(u:Averaging)(he:P.sym.parity z.fieldT.1 z.fieldT.2= if p then -z.fieldT.2 else z.fieldT.2):∀ᶠ i in atTop,∀ U,QCD.Grass.Hom p (signalW u z φ i U):=by
    let d:=z.fieldT.1; let v:= z.fieldT.2; filter_upwards [hφ.eventually (hQ.mixing d)] with i hi U; let F:= P.mix d u (φ i); let X:= P.sym.parity d; have hx:X (F v)= F (X v):= LinearEquiv.congr_fun (hi.parity u) v -- id
    let q: Label d→ₗ[ℂ] Insertion (C.S.side (C.R (φ i)) (C.N (φ i))) 6:=P.candidate d _ (z.r i)
    change X v= _ at he; change QCD.Grass.Hom p (q (F v) U); have h:grade (q (F v) U)=q (X (F v)) U:= congr_fun (hQ.sections.parity ..) U; rw [hx,he] at h; cases p; · exact h
    change grade _=_; simp only [↓reduceIte,map_neg,ContinuousMap.neg_apply] at h; exact h
end Petals
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Petals.tickets
#print axioms YM.Massive.Tarn.Choir.Petals.acted
