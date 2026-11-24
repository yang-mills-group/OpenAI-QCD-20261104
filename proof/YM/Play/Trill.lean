import YM.Play.Fence
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace YM.MassiveQCD.Play
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (M:Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "M'"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
local notation "Β"=>banknote N z' a
variable (Y:Fleet H κ (ample N I))
local notation "Ξ"=> closet H G M X z a
local notation "Tx"=> united (Ξ) Y
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ M)
namespace Camp
open TabletV
variable (p: Finset (Fj D E J))
local notation "V'"=> Wound M
local notation "P'"=> Piece S (Wound M ⊕ κ)
local notation "p'"=> plume P₀ G M p
variable (χ:Chi)(U:Grid c)
open PhysicalNext.Repeat.Greenbelt
variable (hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)
set_option quotPrecheck false
local notation "H'"=> student H G M X z a Y p hk hw hs he
local notation "Zs"=> campus H G M X z a Y p hk hw hs he
local notation "Ip"=> ↥(plume P₀ G M p)
variable {n m d:ℕ}(hS:Gowns G M X z p n (τ:=τ)) (i:Clusters (united (closet H G M X z a) Y).Bright)(hY:(united (closet H G M X z a) Y).Famous)
private lemma coefficientV {κ:Type} (R: κ→κ→Prop) (s:Tuple κ n)(h:Ursell.coefficient R s≠0): Graph.reaches (Ursell.pot R s):=by
    let p:= Ursell.pot R s; have hb:Graph.mass p≠0:= h; unfold Graph.mass at hb
    have hP:(Graph.connectedGroups p).Nonempty:=Finset.nonempty_iff_ne_empty.mpr (fun he=> hb (by rw [he,Finset.sum_empty])); obtain ⟨b,hb⟩:=hP; obtain ⟨hs,hq⟩:=Graph.belongs.mp hb; intro i j; exact Relation.ReflTransGen.mono (r:=Graph.link b) (fun i j h=>⟨h.1,hs h.2⟩) _ _ (hq _ _)
private lemma mergeA {τ:Type*}[Fintype τ][Nonempty τ](v:I→Support c)(m:τ→ Finset I)(f:τ→Support c)(h:∀ i,Ac.Spark v (m i))(hv:∀ i,f i⊆ (m i).biUnion v) (H:∀ i j,Relation.ReflTransGen (fun i j=>¬Disjoint (f i) (f j)) i j): Ac.Spark v (univ.biUnion m):=by
   let W:= univ.biUnion m
   have he i:m i⊆W:= subset_biUnion_of_mem _ (mem_univ i)
   have ht i j k (hj:j∈m i)(hk:k∈m i): Ac.chain v W j k:= Relation.ReflTransGen.mono (p:=Ac.bonds v W) (fun a b h'=>⟨he i h'.1,he i h'.2.1,h'.2.2⟩) _ _ ((h i).2 _ hj _ hk)
   let i:τ:= Classical.arbitrary _; refine ⟨(h i).1.mono (he i),?_⟩; have hc i j (hp:Relation.ReflTransGen (fun i j=> ¬Disjoint (f i) (f j)) i j): ∀ a∈ m i,∀ b∈ m j,Ac.chain v W a b:=by
       induction hp with
       | refl=> exact fun _ ha _ hb=> ht i _ _ ha hb
       | @tail i j _ h₀ ih=>
         intro a ha b hb; obtain ⟨x,hx,hg⟩:=Finset.not_disjoint_iff.mp h₀; obtain ⟨k,hk,hx⟩:=mem_biUnion.mp (hv _ hx); obtain ⟨l,hl,hg⟩:=mem_biUnion.mp (hv _ hg)
         exact Relation.ReflTransGen.trans (Relation.ReflTransGen.tail (ih _ ha _ hk) (show Ac.bonds v W k l from ⟨he _ hk,he _ hl,x,hx,hg⟩)) (ht j _ _ hl hb)
   intro i hi j hj; obtain ⟨p,_,hi⟩:=mem_biUnion.mp hi; obtain ⟨q,_,hj⟩:=mem_biUnion.mp hj; exact hc _ _ (H p q) _ hi _ hj
-- spectral tag (works even with extraneous sails, but Lemma portV for pure)
variable (e₁:κ→Finset I)
def omegaE (e: κ→Finset I): Wound M ⊕ κ → Finset I := Sum.elim (fun (j:Wound M)=> X.markers j.val) e
local notation "Ov"=> omegaE M X e₁
local notation "Rt"=> Ray (z') (n + 45*radiusB τ)
local notation "S₁"=> (Tx).swingE N Ov i -- notation uses.Y
include hS hs he hY hw hk
lemma rawP (h': port H G M X z a Y p χ U i≠0) : Ac.Spark Rt (swingE N (Tx) Ov i) ∧ seatP (Tx).lightF i ⊆ (swingE N (Tx) Ov i).biUnion Rt:=by
   rw [studious H G M X z a Y hw hk p χ U hs he i hY] at h'; split at h'; swap; · exact (h' rfl).elim
   next hp =>
    let D j:= i.2 j; let f j:=(Tx).lightF (D j); let m j:= deathT Ov (D j).val; choose w hw' h using fun j=>mem_image.mp (hp j) -- h shadow
    have hψ j : (D j).val= badge M S κ (child G M p (w j)):=congr_arg Subtype.val (h j).symm
    have hz j : m j = X.markers (w j).val:=by
       unfold m deathT; rw [hψ,badge,show Finset.toRight _ = {Sum.inl (β:=κ) (child G M p (w j))} from ?_,singleton_biUnion]; rfl
       ext; simp
    have hs' j: f j⊆ (m j).biUnion Rt:=by
       rw [hz]; unfold f Fleet.lightF; rw [hψ,partV]; exact panorama G M X z p hs he hS _ (mem_powerset.mp (mem_filter.mp (w j).property).1) ((mem_filter.mp (w j).property).2.2)
    rw [phoenix (Tx) χ U hY] at h' -- rename
    have hg:Ursell.coefficient (blocked (Tx).lightF) D≠0:= fun he=> h' (by unfold termP; dsimp only [D] at he; rw [he,zero_smul,smul_zero])
    refine ⟨mergeA Rt m f (?_) hs' (?_), ?_⟩
    · intro j; rw [hz]; exact kerchief G M X z hw hk p hs he hS (child G M p (w j)) (mem_powerset.mp (mem_filter.mp (w j).property).1) ((mem_filter.mp (w j).property).2.2)
    · intro i j; refine Relation.ReflTransGen.mono (p:=fun i j=>¬Disjoint (f i) (f j)) (fun a b h=>?_) _ _ (coefficientV _ _ hg i j); exact fun hv=> by obtain ⟨i,hi,hj⟩:= literal_test (Tx).lightF (fun i=> i.2.1.1) _ _ (Ursell.allow _ D h); exact Finset.disjoint_left.mp hv hi hj
    intro j hj; obtain ⟨x,hx,hj⟩:=mem_biUnion.mp hj; obtain ⟨l,hl,hj⟩:=mem_biUnion.mp (hs' x hj); exact mem_biUnion.mpr ⟨l,mem_biUnion.mpr ⟨_,hx,hl⟩,hj⟩

-- diameter argument.W
omit hw hk hs he hY hS
lemma ridgeSpan (z:I→Site c)(T:Finset I)(n) (hf:Ac.Spark (Ray z n) T) (i j:I) (hi:i∈T)(hj:j∈T): separation (z i) (z j) ≤ T.card*(2*n):=by
     let f (s:ℕ):= T.filter fun j=> separation (z i) (z j)≤ s*(2*n)
     by_contra! hn; have hP : ∀ s≤T.card,s<(f s).card:=by
         intro s; induction s with
         | zero=> intro _; exact card_pos.mpr ⟨i,mem_filter.mpr ⟨hi,by simp⟩⟩
         | succ s ih=>
            intro hs; have hh:=ih (by omega); refine lt_of_le_of_lt hh ?_; apply Finset.card_lt_card; refine lt_of_le_of_ne (?_) (?_)
            · intro p hp; obtain ⟨hp,hv⟩:= mem_filter.mp hp; exact mem_filter.mpr ⟨hp,hv.trans (Nat.mul_le_mul_right _ (by omega))⟩
            intro h; have h0 j (h':Ac.chain (Ray z n) T i j): j∈ f s := by
                induction h' with
                | refl=> exact mem_filter.mpr ⟨hi,by simp⟩
                | @tail i' j _ hb ih =>
                   rw [h]; obtain ⟨hp,hj,w,hW,hh'⟩:=hb; have H:= (portion _ _ _ _).mp hW; have hp:=(portion _ _ _ _).mp hh'; have hv:= (mem_filter.mp ih).2; refine mem_filter.mpr ⟨hj,(le_trans (separation_triangle (z i) (z i') (z j)) ?_)⟩; have hz:=separation_triangle (z i') w (z j); rw [separation_comm w] at hz; rw [Nat.add_mul, one_mul]; omega
            have hv:= (mem_filter.mp (h0 j (hf.2 _ hi _ hj))).2; exact (not_le_of_gt hn) (hv.trans (Nat.mul_le_mul_right _ (by omega)))
     exact (not_le_of_gt (hP _ le_rfl)) (card_le_card (filter_subset _ _))
end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.rawP
#print axioms YM.MassiveQCD.Play.Camp.ridgeSpan
