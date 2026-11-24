import YM.Lyre.Monument
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV
open MassiveQCD.Play
variable {A B C D I J:Type}[Fintype A][Fintype B][Fintype C][Fintype D][Fintype I][Fintype J]{n:ℕ}
variable (Q:I→Bool)(W:J→Bool)(u:I↪ J)(h:∀ i,W (u i)=Q i)
local notation "PI"=> Spine I
local notation "PJ"=> Spine J
local notation "T" i:arg=> mono (burst Q ({i}:Finset I))
local notation "Tz" i:arg=> mono (burst W ({u i}:Finset J))
variable (M:Matrix A B ℂ)(S: Matrix (Spine I) (Spine J) ℂ)(hP:∀ i:I, staysM S (mono (burst Q {i}))=grade (mono (burst W {u i})))
local notation "θ"=>Matrix.fromBlocks M 0 0 S
variable (s:Fin n→I)(hs:Injective s)
local notation "pin"=> crest s
local notation "rev"=> (Fin.rev :Fin n→ Fin n) -- conflict
local notation "go"=> (u ∘s ∘ rev)
variable (v:J→ℕ)(P: ∀ i:I, Arise.Bill.Cups (v (u i)) (Q i))(P': ∀ i:J, Arise.Bill.Cups (v i) (W i)) (a:Axis) (p:I→ E4) (p':J→E4) (x:E4)
local notation "Z"=> pays (U:=A) Q (v ∘u) p P
local notation "Z'"=> pays (U:=B) W v p' P'
-- arbitrary fixes under a mask. Relabel afterwards.
lemma cover_v (S:Finset I): (S.map u).powerset= S.powerset.image (fun i=> i.map u):=by
   ext i; constructor
   · intro hi; let X:= S.filter fun j=>u j∈i; have hx:X.map u=i:=by
        ext j; simp only [Finset.mem_map]; constructor; · rintro ⟨t,ht,rfl⟩; exact (mem_filter.mp ht).2
        intro ht; obtain ⟨i,hv,rfl⟩:=Finset.mem_map.mp ((mem_powerset.mp hi) ht); exact ⟨i,mem_filter.mpr ⟨hv,ht⟩,rfl⟩
     exact mem_image.mpr ⟨X,mem_powerset.mpr (filter_subset ..),hx⟩
   intro hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact mem_powerset.mpr (map_subset_map.mpr (mem_powerset.mp hj))
lemma markL : Injective (fun i:Finset I=> i.map u):=fun i j h=> Finset.Subset.antisymm -- fix
    ((map_subset_map.mp h.le):i⊆j) (map_subset_map.mp h.ge)
lemma erase_v (v:Finset I): ((v.map u).powerset.erase ∅)= (v.powerset.erase ∅).image (fun i:Finset I=>i.map u):=by rw [cover_v, image_erase (f:=fun i:Finset I=>i.map u) (markL u), map_empty] -- syntax
private lemma windM (i:Finset I)(w:Finset (Finset I)): (w.image (fun j=>j.map u))∈registry (i.map u)↔ w∈registry i:=by
    simp only [registry,mem_filter,mem_powerset]; let f:= fun j:Finset I=>j.map u
    have h:w⊆i.powerset ↔ w.image f ⊆ (i.map u).powerset:=by rw [cover_v, Finset.image_subset_image_iff (markL u)];
    have hp:(∅:Finset I)∈w ↔ (∅:Finset J)∈w.image f:=by rw [← show f ∅=∅ from Finset.map_empty _]; exact ⟨fun h=>mem_image_of_mem _ h,fun he=>by obtain ⟨i,hi,hv⟩:=mem_image.mp he; exact markL u hv ▸ hi⟩ -- edit
    have he: (w.image f).biUnion id = f (w.biUnion id):=by
         ext x; simp only [mem_biUnion,mem_image,id_eq, f,Finset.mem_map]; aesop
    have hg(i j:Finset I): Disjoint (f i) (f j) ↔ Disjoint i j:=by simp [f] -- name
    have ht:(w:Set (Finset I)).PairwiseDisjoint id ↔ ((w.image f):Set (Finset J)).PairwiseDisjoint id:=by
        -- strip edit
        change _↔ ((w.image f):Set (Finset J)).PairwiseDisjoint id; constructor
        · intro i j hj k hk ht; obtain ⟨m,hm,rfl⟩:=mem_image.mp hj; obtain ⟨n,hn,rfl⟩:=mem_image.mp hk; exact (hg _ _).2 (i hm hn (fun h=>ht (congr_arg _ h)))
        intro i j hj k hk ht; exact (hg _ _).1 (i (mem_image_of_mem f hj) (mem_image_of_mem f hk) ((markL u).ne ht))
    change ( (w.image f⊆_) ∧ _∧ (w.image f).biUnion id=f i∧_ )↔ _
    rw [← h,← show (∅:Finset I)∈w ↔ (∅:Finset J)∈w.image f from hp,he,(markL u).eq_iff,ht] -- ht cast
lemma widen (i:Finset I):registry (i.map u)=(registry i).image (fun s=>s.image (fun j=>j.map u)):=by
    let f:= fun j:Finset I=>j.map u; ext w; constructor
    · intro h; have hp:w ⊆ i.powerset.image f :=by rw [show _= (i.map u).powerset from (cover_v u i).symm]; exact mem_powerset.mp (mem_filter.mp h).1
      let x:= i.powerset.filter (fun j=> f j∈w); have he:x.image f=w:=by
           apply Finset.Subset.antisymm; intro a ha; obtain ⟨i,h,rfl⟩:=mem_image.mp ha; exact (mem_filter.mp h).2
           intro a ha; obtain ⟨i,h,rfl⟩:=mem_image.mp (hp ha); exact mem_image_of_mem _ (mem_filter.mpr ⟨h,ha⟩)
      rw[← he] at h; exact mem_image.mpr ⟨x,(windM u i x).1 h,he⟩
    intro h; obtain ⟨t,hh,rfl⟩:=mem_image.mp h; exact (windM u _ t).2 hh
lemma widenC (i:Finset I):Chamber.cut (i.map u)=(Chamber.cut i).image (fun s=>s.image (fun j=>j.map u)):=by
    unfold cut; rw [widen]; rw [Finset.image_erase (f:= fun s:Finset (Finset I)=>s.image (fun j=>j.map u))]; rw [Finset.image_singleton]; exact Finset.image_injective (markL u)
lemma matchLog (X: Finset I→ Patio A)(Y:Finset J→Patio B) (U:Finset I)(he:∀ v⊆ U,Y (v.map u)=antiE M (X v)): ∀ v⊆U, cetacea Y (v.map u)=antiE M (cetacea X v):=by
     let V(i:Finset I):=i.map u -- edit sort
     have hx(i:ℕ):∀ v⊆U,v.card=i →cetacea Y (v.map u)=antiE M (cetacea X v):=by
        induction i using Nat.strong_induction_on with
        | h i ih=>
           intro v h hv; rw[cet,cet]; split_ifs with hg hg' hp
           · rw [he _ h,map_sub,map_sum,widenC, sum_image (f:=(fun i=> ∏ j∈i,cetacea Y j)) (by
                exact Injective.injOn (Finset.image_injective (markL u)))]; refine congr_arg _ (sum_congr rfl fun j hj=>?_)
             rw [prod_image ((markL u).injOn)]
             have he' (s:Finset (Finset I))(hs:s⊆j): ∏ k∈s,cetacea Y (k.map u)=antiE M (∏ k∈s,cetacea X k):=by
                induction s using Finset.induction_on with| empty=> rw [prod_empty,prod_empty,anti_one] |insert a b ha ig=> let h':= hs (mem_insert_self ..); rw [prod_insert ha,prod_insert ha,anti_m,ig ((subset_insert ..).trans hs), ih _ (hv ▸ card_lt_card (limit hj h')) _ ((member (mem_of_mem_erase hj) h').2.trans h) rfl]
             exact he' _ le_rfl
           · exact False.elim (hg' ((map_nonempty ..).mp hg))
           · exact False.elim (hg ((map_nonempty ..).mpr hp))
           exact (map_zero _).symm
     exact fun v h=> hx v.card v h rfl
-- physical consequence
variable (K:Finset I)(hp:Set.InjOn p K) (hm:∀ i∈ K,p' (u i)= UV.Free.Lyre.crossV a x p i) (hΦ:∀ i∈K, Arise.Bill.meaning (v (u i)) (W (u i)) (P' (u i))= UV.adj a (Arise.Bill.meaning (v (u i)) (Q i) (P i)))
include h hP hm hΦ hp
lemma shores (i:Finset I)(hx:i⊆K): antiE θ (cetacea Z i)= cetacea Z' (i.map u):=by
    symm; apply matchLog u θ _ _ K (?_) i hx; intro U ht; let s:=Quills.tour U
    have hs: Quills.crest s=U:= club _
    have he(j:Fin U.card):s j∈ K:= ht (hs ▸ (exists_fix ..).2 ⟨j,rfl⟩)
    have hL: Injective (p ∘ s):=fun j k h=> snug U (hp (he j) (he k) h)
    rw [← hs]; exact (placard Q W u h M S hP s (snug U) v P P' a p p' x (fun i hi=> hm i (ht (hs ▸ hi))) (fun i hi=> hΦ i (ht (hs ▸ hi))) hL).symm
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.shores
