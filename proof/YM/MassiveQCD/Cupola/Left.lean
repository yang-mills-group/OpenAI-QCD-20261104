import YM.MassiveQCD.Cupola.Foil
/-! # Truncation to body (no marker) commutes with every layout.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open QCD QCD.Grass QCD.Cove QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Function Loom
open MeasureTheory NormedSpace Filter
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B:Type}[Fintype A][Fintype B]
variable (B)
-- generic scrap-empty morphism. all: changeVars
noncomputable def resetM (A:Type)[Fintype A] : Alg (A⊕B)→ₐ[ℂ] Alg A:=changeVars (exit Embedding.inl)
lemma frozen (x:Alg A): resetM B A (fiber B x)=x:= exitBack Embedding.inl x
lemma judgeB (s:Finset B) (x:Alg A): resetM B A (stake A s x)=if s=∅ then x else 0:=by
   split; next he=> rw [he,quiet]; exact frozen ..
   next he=>
     rw [markedOut,map_mul]; obtain ⟨w,hw,hS,hX⟩:= expression s
     rw [hX,map_list_prod,map_list_prod]; rw [show (List.map _ (List.map _ (List.ofFn (Grass.atom ∘ w)))).prod= (0:Alg A) from ?_,mul_zero] -- syntax
     obtain ⟨i,h⟩:=Finset.nonempty_iff_ne_empty.mpr he; obtain ⟨j,hj⟩:= (hS i).1 h; simp only [List.map_ofFn]; -- noncomm prod_zero
     have hp (u): resetM B A (quill A (atom (w u)))=0:=by rw [quill, embed_atom, resetM, change_atom]; apply sum_eq_zero; intro i hi; unfold exit; rw [if_neg (show _ from by apply Sum.inl_ne_inr), zero_smul]
     exact List.prod_eq_zero (List.mem_ofFn.mpr ⟨j,hp j⟩) -- check
lemma revive (x:Alg (A⊕B)): resetM B A x=scrape A ∅ x:=by
   conv_lhs=> rw [← rewriteR A x,map_sum]
   rw [sum_eq_single ∅]; rw [judgeB,if_pos rfl]; exact fun i _ h=> (judgeB B i _).trans (if_neg h); simp
open Stitch
noncomputable def vacR (A:Type)[Fintype A] : Patio (A⊕B)→ₐ[ℂ] Patio A:= car (resetM B A) fun _x h=> (exterior_parity _ _).trans (congr_arg _ h)
noncomputable def rootR (A:Type)[Fintype A] : Patio A→ₐ[ℂ]Patio (A⊕B):=car (fiber B) fun _x h=> (embed_grade ..).trans (congr_arg _ h)
lemma off (x:Patio A) : vacR B A (rootR B A x)=x:= Subtype.ext (frozen ..)
variable {N:ℕ}{c f:Side}{S:Ratio c f}{E J D I:Type}[Fintype I]
open Patron Sway OrbitG Villa Apron
variable {P:Rise f N E J}(Y:Stitch.Tablet P I) (G: Send S N D)
structure Neat :Prop where
    main i U : vacR (Spine I) (Keys f N) (Y.main i U)=P.main i U
    plug i U : vacR (Spine I) (Keys f N) (Y.plug i U)=P.plug i U
section neat
variable (h:Neat Y)(t:ℝ)(V:Grid f)(s:Finset (Fj D E J))
include h
lemma throughR : vacR (Spine I) (Keys f N) (Y.made t V s)=made P t V s:=by
    let Z:= vacR (Spine I) (Keys f N)
    have he i : Z (Y.read t V i)=P.reading t V i:=by
        unfold Tablet.read Rise.reading; by_cases hp:Healthy t (P.row i).support V; · rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp]; exact h.main i V
        rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,map_zero]
    change Z _=_; unfold Tablet.made made; rw [map_mul,map_prod,map_prod]; apply congr_arg₂ (·*·)
    exact prod_congr rfl fun i _=> by rw [map_sub,map_one,NormedSpace.map_exp Z Z.toLinearMap.toContinuousLinearMap.continuous, he]
    exact prod_congr rfl (fun i _=> h.plug i V)
lemma hueR : vacR (Spine I) (Keys c N) (Y.hue t G s V)= Cove.hue G P t s V:=by
    unfold Tablet.hue hue; split; swap; · exact map_zero _
    apply Subtype.ext; let Z:= Tablet.tunnel G s V; change resetM (Spine I) (Keys c N) (carry _ Z _)= _; rw [revive,wing,← revive]; -- `dipping`
    exact (congr_arg Z (congr_arg (fun i:EvenA f N=> i.val) (throughR Y h t V s))).trans (dipping G P t s V).symm
end neat
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.hueR
