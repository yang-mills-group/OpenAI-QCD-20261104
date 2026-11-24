import YM.Gust.Fez
import YM.Gust.Pitch
set_option maxHeartbeats 480000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala Marque
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){m n k:ℕ} (a:Axis)
include hK hf
lemma lotus (v:List (Marque T))(hX:Strip.distinct (lands v))(hn:∀ i∈v, i.p≠0)(hi:∀ i∈v,∃ t,i.x=pet a t)(hp:grades v=1):∃ n:ℕ,∃ p:Gala T n, wall p 0=lands v∧ Visible p:=by
       have h(N:ℕ)(v:List (Marque T))(ht:v.length=N)(hX:Strip.distinct (lands v))(hn:∀ i∈v,i.p≠0)(hi:∀ i∈v,∃ t,i.x=pet a t)(hp:grades v=1):∃ n:ℕ,∃ p:Gala T n, wall p 0=lands v∧ Visible p:=by
           induction N using Nat.strong_induction_on generalizing v with
           | h N ih=>
             cases v with
             | nil=> exact ⟨0,[],rfl, fun i=>Fin.elim0 i⟩
             | cons i v=>
                 cases h:i.q
                 · obtain ⟨n,w,he,hW⟩:= ih v.length (by simp [←ht]) v rfl (by exact Strip.fresh _ hX) (fun i h=> hn _ (List.mem_cons_of_mem _ h)) (fun i h=> hi _ (List.mem_cons_of_mem _ h)) (by simpa only [grades,List.map_cons,tauMod,List.prod_cons,h,Bool.false_eq_true,↓reduceIte,one_mul] using hp)
                   let X:= passP hf n i.p (h ▸ i.h); let W:Gala T n:= (i.x,X)::w; have hh:wall W 0=lands (i::v):=by unfold W wall lands; simp only [List.map_cons]; exact congr_arg _ he
                   refine ⟨n,W,hh,fun j=> ?_⟩; have hu: Piers W:=by rw[←hh] at hX; simpa only[Piers,wall,List.map_map,comp_def] using ((spots _).1 hX)
                   change tone ((i.x,lampU P K)::wall w j.succ)≠0; rw [unit_first hf _ _ (length_ok W hu j.succ)]; exact hW j
                 · have hx: grades v= -1:=by change tauMod i.q*grades v=1 at hp; rw[h,show tauMod true=(-1:ℂ) from rfl,neg_one_mul] at hp; exact neg_eq_iff_eq_neg.mp hp
                   obtain ⟨p,l,z,rfl,hp,hz⟩:= discover v hx; have hh:List.Sublist (l++z) (i::(l++p::z)):= ((List.sublist_cons_self p z).append_left l).cons i
                   obtain ⟨n,L,hL,hζ⟩:=ih (l++z).length (by rw [←ht]; simp) (l++z) rfl ((spots _).mpr (((hh.map _).map _).nodup ((spots _).1 hX))) (fun i h=> hn _ (hh.subset h)) (fun i h=>hi _ (hh.subset h)) hz
                   rw [lands,List.map_append] at hL; obtain ⟨A,B,rfl,r,s⟩:= Marque.organized L hL; exact ⟨_,Marque.pairsR hK hf a i p l z _ _ h hp hX (hi i (by simp)) (hi p (by simp)) (hn _ (by simp)) r s hζ⟩
       exact h _ v rfl hX hn hi hp
end YM.Massive.Gust
#print axioms YM.Massive.Gust.lotus
