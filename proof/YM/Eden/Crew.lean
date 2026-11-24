import YM.Eden.Pig
/-! # lower profile challenge.Budget sleeves. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek
variable (P:Symmetric (Tube su d))(V:Matrix (Sings d) (Sings d) ℂ)
structure Farm (P:Symmetric (Tube su d))(V:Matrix (Sings d) (Sings d) ℂ)(X:ℝ): Prop where
   hi:0≤ X
   score i j : ‖P.cov i j‖≤ X
   price i j : ‖V i j‖≤ X
noncomputable def vessel (P:Symmetric (Tube su d))(V:Matrix (Sings d) (Sings d) ℂ): Module.End ℂ (Bard d):=TensorProduct.map (milk P) (QCD.Creek.birth (Wand V)).toLinearMap
local notation "Ph"=> vessel P V
local notation "Q"=> Pad d
local notation "Y"=> motto
variable (p:Lp d)(q:Lq d)(C:ℝ)
noncomputable def raysL (l k:ℕ):Set (Pad d):={x|x.1.length ≤ l ∧ x.2.length ≤ k∧ x.1.length+x.2.length < l+k}
lemma raysR (d:ℕ)(l k:ℕ) : (raysL (d:=d) l k).Finite:=by
    have h {A:Type}[Fintype A](i:ℕ) : Set.Finite {x:List A|x.length ≤ i}:= by induction i with
     | zero=> simpa using (Set.finite_singleton ([]:List A))
     | succ i ih=>
       let S:= (Set.finite_univ (α:=A)).prod ih; apply ((S.image (fun x=>x.1 :: x.2)).insert []).subset; rintro (_|⟨u,x⟩) hp
       · exact Set.mem_insert _ _
       exact .inr ⟨⟨u,x⟩,⟨Set.mem_univ _,Nat.le_of_succ_le_succ hp⟩,rfl⟩
    exact (Set.Finite.prod (h (A:=Tube su d) l) (h (A:=Sings d) k)).subset (fun x hx=>⟨hx.1,hx.2.1⟩)
noncomputable def stip (v:ℕ)(C:ℝ) :ℕ→ℝ
    | 0=>0
    | k+1=> stip v C k+(v:ℝ)*(C+C)*(stip v C k+1)
lemma stip_nn (v k:ℕ)(h:0≤C):0 ≤ stip v C k:=by induction k with|zero=> exact le_rfl|succ k ik=>rw[stip,mul_assoc]; positivity
lemma fullQuota {z :Pad d} {i k:ℕ}{C':ℝ}(hz:z∈ raysL i k)(h:Quota Y (raysL z.1.length z.2.length) (Ph (Y z)-Y z) C') : Quota Y (raysL i k) (Ph (Y z)) (C'+1):=by
    refine (sub_add_cancel (Ph (Y z)) (Y z) ▸ (?_:Quota Y (raysL i k) (Ph (Y z)-Y z + Y z) (C'+1))); apply (h.mono ?_ le_rfl).joins (ticksY _ hz)
    intro i hi; exact ⟨hi.1.trans hz.1,hi.2.1.trans hz.2.1,hi.2.2.trans hz.2.2⟩
lemma shapes (h:Farm P V C)(n k:ℕ)(ht:k≤n): ∀ z:Pad d,z.1.length+z.2.length≤ k→ Quota Y (raysL z.1.length z.2.length) (Ph (Y z)- Y z) (stip n C k):=by
    induction k with
    | zero=>
       rintro ⟨p,q⟩ hh; change p.length+q.length ≤0 at hh; simp only [Nat.le_zero, Nat.add_eq_zero,List.length_eq_zero_iff] at hh; obtain ⟨rfl,rfl⟩:=hh; rw[show Ph (Y ([],[]))= motto ([],[]) from ?_,sub_self]; · exact sterile _ le_rfl
       unfold vessel motto; rw [TensorProduct.map_tmul]; change milk P (1:poly _) ⊗ₜ[ℂ] QCD.Creek.birth (Wand V) 1= motto ([],[]); rw [pure, Arise.Pair.emptyW]; rfl
    | succ k ih=>
      let X:=stip n C k; have hX:= stip_nn C n k h.hi; let β:ℝ:= (C+C)*(X+1); have hb:0 ≤ β:=mul_nonneg (add_nonneg h.hi h.hi) (add_nonneg hX zero_le_one)
      rintro ⟨p,q⟩ hh; change p.length+q.length ≤ k+1 at hh; specialize ih (by omega:k≤n)
      by_cases ht':p=[] ∧ q=[]
      · obtain ⟨rfl,rfl⟩:=ht'; have hf:=ih ([],[]) (Nat.zero_le k); rw[stip,mul_assoc]; exact hf.mono (Set.Subset.refl _) (le_add_of_nonneg_right (show 0 ≤ n*β from mul_nonneg (by positivity) hb))
      cases p with
      | cons a p=>
         let Y₀:=motto (p,q); let W:= Gχ a
         let u:Pad d→ Pad d:= fun i=> (a::i.1,i.2); rw [show Ph (Y (a::p,q)) = _ from attestG a p q, compoG a p q];
         have hT:Set.MapsTo u (raysL p.length q.length) (raysL (a::p).length q.length):=by
              rintro ⟨v,V⟩ ⟨h,ht,hp⟩; exact ⟨Nat.add_le_add_right h _,ht,by change (a::v).length+V.length< (a::p).length+q.length; simp_rw [List.length_cons]; change v.length+V.length<p.length+q.length at hp; omega⟩
         let H:=raysL (d:=d) (a::p).length q.length; let L(i:Fin p.length):Pad d:=(p.eraseIdx i.val,q); let R(i:Fin p.length):= P.cov a (p.get i) • Ph (motto (L i)); have hv :Quota Y H (W*(Ph Y₀-Y₀)) X:= (ih (p,q) (by change p.length+q.length≤ k; simp only [List.length_cons] at hh; omega)).down (LinearMap.mulLeft ℂ W) u hT (fun i _=>(compoG ..).symm)
         have hp(i:Fin p.length): Quota Y H (Ph (Y (L i))) (X+1):=by
              have he(i:Fin p.length): (p.eraseIdx i.val).length=p.length-1:=List.length_eraseIdx_of_lt i.isLt; refine fullQuota _ _ ⟨?_,le_rfl,?_⟩ (ih (L i) ?_)
              all_goals unfold L; simp only [he,List.length_cons] at *; omega
         have hQ(i:Fin p.length): Quota Y H (R i) β:= ((hp i).scale (P.cov a (p.get i))).mono (Set.Subset.refl _) (mul_le_mul_of_nonneg_right ((h.score ..).trans (le_add_of_nonneg_right h.hi)) (add_nonneg hX zero_le_one))
         change Quota _ H (W*Ph Y₀+ (∑ i,R i)-W*Y₀) _; rw [add_sub_right_comm, ← mul_sub]; apply (hv.joins (Quota.sums univ R _ (fun i _=>hQ i))).mono (Set.Subset.refl _); rw [sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin,stip,mul_assoc]; exact add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simp only[List.length_cons] at hh; omega)) hb) _
      | nil=> cases q with
       | nil=> simp at ht'
       | cons a q=>
         let Y₀:=motto ([],q); let W:=Gξ a; let u:Pad d→ Pad d:= fun i=> (i.1,a::i.2); rw[show Ph (Y ([],a::q))= _ from attestS a q,compoS];
         have hf(i:Pad d)(h:i∈ raysL 0 q.length): i.1=[]:= List.length_eq_zero_iff.mp (Nat.le_zero.mp h.1)
         have hT:Set.MapsTo u (raysL 0 q.length) (raysL 0 (a::q).length):=by rintro ⟨v,V⟩ ⟨h,ht,hp⟩; exact ⟨h,Nat.add_le_add_right ht _,by change v.length+(a::V).length < 0+(a::q).length; simp_rw [List.length_cons]; change v.length+V.length<0+q.length at hp; omega⟩
         let H:=raysL (d:=d) 0 (a::q).length; let L(i:Fin q.length):Pad d:=([],q.eraseIdx i.val); let R(i:Fin q.length):=dollars V a q i • Ph (motto (L i)); have hv:Quota Y H (W*(Ph Y₀-Y₀)) X:= (ih ([],q) (by change 0+q.length≤ k; simp only [List.length_nil,List.length_cons] at hh; omega)).down (LinearMap.mulLeft ℂ W) u hT (fun i hi=> by change W * Y i= Y (i.1,a::i.2); have hh:=hf i hi; cases i with | mk p q=> simp only at hh; subst p; exact (compoS ..).symm)
         have hp(i:Fin q.length) : Quota Y H (Ph (Y (L i))) (X+1):=by
              have he(i:Fin q.length): (q.eraseIdx i.val).length=q.length-1:=List.length_eraseIdx_of_lt i.isLt; refine fullQuota _ _ ⟨le_rfl,?_,?_⟩ (ih (L i) ?_)
              all_goals unfold L; simp only [List.length_nil,he,List.length_cons] at hh ⊢ <;> omega
         have hL(i:Fin q.length): ‖dollars V a q i‖ ≤ C+C:=by unfold dollars; rw[norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]; exact (norm_sub_le ..).trans (add_le_add (h.price ..) (h.price ..))
         have hQ(i:Fin q.length): Quota Y H (R i) β:= ((hp i).scale (dollars V a q i)).mono (Set.Subset.refl _) (mul_le_mul_of_nonneg_right (hL i) (add_nonneg hX zero_le_one)); change Quota _ H (W* Ph Y₀+ (∑ i,R i)-W*Y₀) _; rw [add_sub_right_comm, ← mul_sub]; apply (hv.joins (Quota.sums univ R _ (fun i _=>hQ i))).mono (Set.Subset.refl _); rw [sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin,stip,mul_assoc]; exact add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simp only[List.length_cons,List.length_nil] at hh; omega)) hb) _
end YM.Eden
#print axioms YM.Eden.shapes
