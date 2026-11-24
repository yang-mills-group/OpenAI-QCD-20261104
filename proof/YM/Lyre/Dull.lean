import YM.Lyre.Ruling
import YM.Magi.Glow
/-!
 # C-number representation of all correction histories. Keep degree/cost audits.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
-- Polite AND pure-matter-free. Choices to core same.ALL.
variable (Q:I→Bool)(w:I→ℕ)(U: ∀ i:I,Cups (w i) (Q i))(x:I→E4)(v:Finset I)
local notation "z₁" T=> pays (U:=T) Q w x U
lemma saysE (h:Set.InjOn x (v:Set I)) : ∃ t: Alg (Spine I), Plus t∧ ∀ (A:Type) [Fintype A], ((z₁ A) v).val = quill A t:=by
     let s:=tour v
     let c:= UV.Free.moment (w ∘s) (points (x∘s)) (fun i=> meaning _ _ (U (s i)))
     let T:= c • armature Q s
     have he(i:Fin v.card): s i∈ v:=by have he: s i∈ Quills.crest s:= (exists_fix ..).2 ⟨i,rfl⟩; rwa [show Quills.crest s=v from club v] at he
     have hp:points (x∘s)∈conf v.card:=fun i j h'=> snug v (h (he i) (he j) h')
     have hf(A:Type)[Fintype A]: ((z₁ A) v).val=quill A T:=by
        have H:=colored Q w x s U (snug v) hp (U:=A); unfold pays; rw [show Quills.crest s=v from club v] at H; rw[H,map_smul,map_one,smul_mul_assoc,one_mul]; exact (map_smul ..).symm -- rw dep at H
     refine ⟨T,?_,hf⟩
     let W:=Fin 0; have hy : Plus (((z₁ (Fin 0)) v).val):=((z₁ (Fin 0)) v).property; rw [hf] at hy
     have he(T:Alg (Spine I)): embed (Sum.elim (Fin.elim0 (α:=Spine I)) id) (quill (Fin 0) T)=T:=by rw [quill,embed_comp]; change embed id T=T; rw [embed_id]; rfl
     have hb: quill (Fin 0) (grade T)=quill (Fin 0) T:= (embed_grade (B:= Fin 0 ⊕ Spine I) Sum.inr T).symm.trans hy
     change grade T=T; nth_rw 1[← he (grade T)]; rw [hb,he]
lemma saysECanon (h:Set.InjOn x (v:Set I))(A:Type)[Fintype A]: Polite Q v ((z₁ A) v):= canon Q x U v h v le_rfl
local notation "ϖ" T=> cetacea (z₁ T)
-- actual addition.T per-mask simultaneously: pure red.T mapped onto extended energy via algHom
noncomputable def qraft (A B:Type)[Fintype A][Fintype B]: Patio B→ₐ[ℂ] Patio (A⊕B):= QCD.Cove.car (quill A) fun _ h=> (embed_grade ..).trans (congr_arg _ h)
noncomputable def Honest (Q:I→Bool)(k:Finset I)(t: Patio (Spine I)): Prop:= ∀ (A:Type)[Fintype A], Polite Q k (qraft A _ t)
lemma artwork (h:Set.InjOn x (v:Set I)) : ∃ F: Finset I→ Patio (Spine I), (∀ p⊆v,Honest Q p (F p)∧ ∀ (A:Type)[Fintype A], (z₁ A) p=qraft A _ (F p)) ∧ F ∅=1:=by
    choose G he using fun p :Finset I=> show ∃ M: Patio (Spine I), p ⊆ v→ Honest Q p M∧ ∀ (A:Type)[Fintype A], (z₁ A) p=qraft A _ M from (by
           by_cases hp:p ⊆ v
           · have ht:Set.InjOn x (p:Set I):= h.mono hp; obtain ⟨t,hx,hg⟩:=saysE Q w U x p ht; let M: Patio (Spine I):=⟨t,hx⟩; have hv(A:Type)[Fintype A]:(z₁ A) p=qraft A _ M:= Subtype.ext (hg A); exact ⟨M,fun _=>⟨fun a b=>by rw [← hv]; exact saysECanon Q w U x p ht a, hv⟩⟩
           exact ⟨0,fun h'=> (hp h').elim⟩)
    -- F ∅ directly prescribe identity; needs `pays.. ∅=1` regardless.
    refine ⟨fun i=> if i=∅ then 1 else G i,fun p hp=> by
         dsimp only; split; next h=>subst p; refine ⟨fun A _=> by rw[map_one]; exact polite_empty_one _,fun A _=>?_⟩; unfold pays; rw [prod_empty, Vest.Tone.read,Bera.alights,map_one,map_one]; -- inspect below
         next h=> exact he p hp,if_pos rfl⟩
lemma honorG (F: Finset I→ Patio (Spine I)) (hp:∀ i⊆v,Honest Q i (F i)) (p:Finset I)(hx:p⊆v)(U':Finset I) (A:Type)[Fintype A](Y: Finset I→Patio (A⊕Spine I))(hY:∀ i⊆v,Y i=qraft A _ (F i)):
    Honest Q p (cetacea F p) ∧ cetacea Y p=qraft A _ (cetacea F p):=by
    have he(A:Type)[Fintype A](Y : Finset I→Patio (A⊕Spine I))(hY: ∀ i⊆v,Y i=qraft A _ (F i)): ∀ i⊆v,cetacea Y i=qraft A _ (cetacea F i):=by
         suffices h:∀ j:ℕ,∀ i⊆v,i.card=j→cetacea Y i=qraft A _ (cetacea F i) from fun i hi=>h _ _ hi rfl
         intro j; induction j using Nat.strong_induction_on with
         | h j ih=>
            intro i hi he; rw [cet,cet]; split; next h=> rw [hY i hi,map_sub,map_sum]; apply congr_arg; refine sum_congr rfl fun k hk=>?_ ; rw [map_prod]; exact prod_congr rfl fun i' hi'=> ih _ (he ▸ card_lt_card (limit hk hi')) _ ((member (mem_of_mem_erase hk) hi').2.trans hi) rfl
            rw [map_zero]
    refine ⟨fun B _=>?_, he A Y hY _ hx⟩
    let T:=qraft B (Spine I) ∘ F; rw [← he B T (fun _ _=>rfl) _ hx]; exact cens_log Q T p fun i hi _=> hp i (hi.trans hx) _
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.saysE
#print axioms YM.MassiveQCD.Sample.Quills.Eden.artwork
#print axioms YM.MassiveQCD.Sample.Quills.Eden.honorG
