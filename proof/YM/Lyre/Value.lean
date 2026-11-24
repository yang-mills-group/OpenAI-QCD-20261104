import YM.Lyre.Cubes
/-! # C-number cost literacy at value projection. Valid simultaneous moments between any two price spaces along the path. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter Stitch Stitch.Tablet
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open FlareV
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
variable (Q:I→Bool)(p v:Finset I) (t: Patio (Spine I))
local notation "Z"=> Patio (A⊕Spine I)
local notation "Z'" => Patio (B⊕Spine I)
variable (X: Patio (A⊕Spine I)) (ht:Honest Q p t)
private lemma assigned (h:p⊆ v) : burst Q v \burst Q p=burst Q (v \p):=by
    have he : v=(v\p)∪p:=(Finset.sdiff_union_of_subset h).symm; calc
     _= (burst Q (v\p)∪burst Q p)\burst Q p:=congr_arg (fun T=>T\_) ((congr_arg (burst Q) he).trans (pulver ..))
     _ = _:=by have hv:= (crossedR Q (v\p) p).2 disjoint_sdiff_self_left; ext x; have h:= fun h:x∈burst Q (v \p)=> fun i:x∈burst Q p=>Finset.disjoint_left.mp hv h i; simp; tauto -- `tauto` hv not used edit
noncomputable def flux :ℂ:= coef (burst Q v) (mono (burst Q v \burst Q p)*t.val)
include ht
lemma skint (hv:¬p⊆v): pluck A (burst Q v) (X*qraft A _ t)=0:=by
      apply Eq.trans ?_ (map_zero (pluck A (burst Q v))); apply phoenixC A (T:=v)
      · rw[map_mul, stamen_h A Q p v _ (ht _), if_neg hv,mul_zero,map_zero]
      exact located Q v -- syntax phoenix order
lemma salary (hv:p⊆v) : pluck A (burst Q v) (X*qraft A _ t)=flux Q p v t • pluck A (burst Q (v\p)) X:=by
    change scrape A _ (X.val* quill _ t.val)= _
    let x:=burst Q p; let v':=burst Q v; let s:=v' \x; let g:=coef x t.val
    nth_rw 1 [← Ribbon.rewriteR A X.val]; rw [Finset.sum_mul,map_sum,sum_eq_single s]
    · rw [markedOut,mul_assoc,← map_mul,plucks,show s= _ from assigned Q p v hv]; unfold flux; rw [assigned Q p v hv]; rfl
    intro i hi hh; rw [markedOut,mul_assoc,← map_mul,plucks]; rw [coatC Q p t ht]; change coef v' (mono i*(g • mono x)) • _=_; rw [mul_smul_comm,map_smul]; by_cases he:Disjoint i x
    · have h: v'≠ i∪x:=by intro h; apply hh; unfold s; rw[h]; ext a; have ht := fun ha:a∈i=> fun h':a∈x=>Finset.disjoint_left.mp he ha h'; simp; tauto
      rcases Grass.mono_mul_sign i x he with H|H <;> rw [H,disjUnion_eq_union] <;> simp only [map_neg,Grass.read_other _ _ h,neg_zero,smul_zero,zero_smul]
    rw [mono_mul_zero _ _ he,map_zero, smul_zero,zero_smul]
    simp
omit ht
variable (s:Fin n→I)(w:I→ℝ)
lemma scale_read : numbered Q A s (capstone A w X)= give w (crest s) • numbered Q A s X:=by
    unfold numbered; simp only [ContinuousLinearMap.smul_apply]; rw [patrol,attuned,smul_comm]
-- valid incidence system witnessed by true proofs
variable {C D:Type}(Λ:Submodule ℂ ((C→ Alg A) × (D→ Alg B)))
def VoiceL (Y:C→Patio (A⊕Spine I))(Y':D→Patio (B⊕Spine I)) := ∀ i ⊆ v,( (pluck A (burst Q i) ∘ Y),(pluck B (burst Q i) ∘ Y'))∈ Λ
variable (Y:C→ Patio (A⊕Spine I))(Y':D→Patio (B⊕Spine I))
lemma by_read (h:∀ (n:ℕ) (s:Fin n→I),Injective s → crest s⊆ v→((numbered Q A s∘Y),(numbered Q B s ∘ Y'))∈Λ): VoiceL Q v Λ Y Y':=by
    intro i hi; let f:=tour i; have hz:signG Q f* signG Q f=1:=(arm_bill Q f (snug i)).2.1; have he:=Λ.smul_mem (signG Q f) (h _ f (snug i) (show crest f⊆v from (club i).symm ▸ hi))
    simp only [Prod.smul_mk,numbered] at he; let P:=burst Q i; rw [show crest f=_ from club _] at he
    have hv(A X:Type)[Fintype A](Y:X→ Patio (A ⊕ Spine I)): signG Q f • ((signG Q f • pluck A P)∘Y) = pluck A P ∘Y:=by funext x; change signG Q f • signG Q f • (pluck A P (Y x))=_; rw [smul_smul,hz,one_smul]; rfl
    exact hv A C Y ▸ hv B D Y' ▸ he -- placeholder trans
lemma to_read (he:VoiceL Q v Λ Y Y')(hg:crest s⊆v) : ((numbered Q A s ∘ Y),(numbered Q B s ∘Y'))∈Λ:= Λ.smul_mem (signG Q s) (he _ hg)
variable (he:VoiceL Q v Λ Y Y')
include he
lemma standingL : VoiceL Q v Λ (fun c=>capstone A w (Y c)) (fun c=>capstone B w (Y' c)):=by
    intro i hi; let K:=burst Q i
    let z:=give w i
    have hL(A C:Type)[Fintype A](X:C→Patio (A⊕Spine I)): pluck A K∘(fun c=>capstone A w (X c))= z • (pluck A K∘X):=funext fun _=> by dsimp only [Function.comp_apply]; rw[patrol, show ignites w K=_ from attuned ..]; rfl
    change (pluck A K ∘_,pluck B K∘_)∈Λ; rw [hL A C,hL B D]; exact Λ.smul_mem z (he _ hi)
lemma adding (hp:Honest Q p t)(ht:p.Nonempty) : VoiceL Q v Λ (fun c=>Y c*NormedSpace.exp (qraft A _ t)) (fun D=>Y' D*NormedSpace.exp (qraft B _ t)):=by
    intro i hi; let K:=burst Q i
    have hvX(A X:Type)[Fintype A](Y:X→ Patio (A⊕Spine I)): pluck A K∘(fun c=> Y c*NormedSpace.exp (qraft A _ t))= (pluck A K ∘ Y) + if p⊆i then flux Q p i t • (pluck A (burst Q (i \p)) ∘ Y) else 0:=by
       split; next hx=> exact funext fun z=>by dsimp only [Function.comp_apply]; rw[Play.Chamber.launch (f:=qraft A (Spine I) t) (q:=Q) (X:=p) (hp A) ht,mul_add,mul_one,map_add,salary Q p i t (Y z) hp hx]; rfl
       next hx=>rw [add_zero]; exact funext fun z=>by dsimp only [Function.comp_apply]; rw[Play.Chamber.launch (f:=qraft A (Spine I) t) (q:=Q) (X:=p) (hp A) ht,mul_add,mul_one,map_add,skint Q p i t (Y z) hp hx,add_zero]
    change (pluck A K∘_, pluck B K∘_)∈Λ; rw [hvX A C,hvX B D]; split; · exact Λ.add_mem (he _ hi) (Λ.smul_mem (flux ..) (he _ (sdiff_subset.trans hi)))
    rw [add_zero,add_zero]; exact he _ hi
omit he
lemma treatments (he:VoiceL Q v Λ Y Y')(G:Finset (Finset I))(K:Finset I→ Patio (Spine I))(hG:∀ i∈G, Honest Q i (K i) ∧ i.Nonempty):VoiceL Q v Λ (fun c=>Y c * NormedSpace.exp (∑ i∈G,qraft A _ (K i))) (fun d=>Y' d* NormedSpace.exp (∑ i∈G,qraft B _ (K i))):=by
    induction G using Finset.induction_on with
    | empty=>simp_rw [sum_empty,NormedSpace.exp_zero,mul_one]; exact he
    | insert a s ha ih=> let ht:=ih (fun i hi=>hG i (mem_insert_of_mem hi)); let H:=hG a (mem_insert_self ..); have h:=adding Q a v (K a) Λ _ _ ht H.1 H.2; simp_rw [sum_insert ha,NormedSpace.exp_add, mul_comm (NormedSpace.exp (qraft _ _ (K _))),← mul_assoc]; exact h
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.treatments
#print axioms YM.MassiveQCD.Sample.Quills.Eden.by_read
