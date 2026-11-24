import YM.Play.Burr
import YM.Mills.VaultD
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U N)
local notation "X'" => loommark I (sailP H Γ N)
local notation "Vx" => tableau L' d K P₀ H G U Γ
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
open Anomaly Play Chamber Camp Cupola
open Stitch Stitch.Tablet
local notation "Ip"=> Wound Zⁱ
local notation "X0"=> Keys f N ⊕ Spine I
local notation "X1"=> Keys c N ⊕ Spine I
local notation "K0"=> Keys f N
local notation "K1"=> Keys c N
variable {m₁:ℕ}
namespace Grove
-- degree on arbitrary subsets.D
set_option quotPrecheck false
local notation "Pe" e=> Fj.pin (picksV f m (radiusB τ)) e (∅:Finset J)
local notation "lk"=> (S').ratio.parent∘ A
local notation "T0"=> (withdraw N ((S').ratio.parent ∘ A) φ)
local notation "Oi"=> omegaE Zⁱ Y (fun (_:Varn f c ⊕ Gaze c)=> ∅)
local notation "inH" => (united U' X')
local notation "sM"=> (swingE N (Tx) (Oi))
variable (e:Finset E)(Z:Finset I)
variable {q₀:I→Bool} {θ α:ℝ}
variable (χ:Chi)(V:Grid c)(p':Wound (roof (G.equip N (radiusB τ)) P₀ 30 (radiusB τ)) ⊕ Varn f c⊕Gaze c →ℝ)
variable (hF:Registry L' d K H G U Γ Y A φ p' θ α q₀ χ)
variable (hR: Fleet.Regal N ((Flight.visit L' K d).ratio.parent ∘ A) φ q₀ (vantage L' d K H G U Γ Y A φ) (Sum.elim (fun w=>Y.markers w.val) (fun _=>∅))) -- Aura bargain
variable (hE:∀ i∈ e,(Y.spine i).Nonempty)
include hF
-- common permitted e all marks in tile; filter each shade
abbrev fled (e:Finset E)(x:Finset I): Finset E:=e.filter fun i=> Y.spine i⊆ x
local notation "At" e=> Play.Camp.port H Z' Zⁱ Y A φ inH (Pe e)
def game (Z:Finset I)(V:Grid c)(i:Clusters (Tx).Bright):= if Z.Nonempty ∧ (sM) i= Z then (At (fled Y e Z)) χ V i else 0
-- price all
lemma gate_sum (Z:Finset I): Summable (game L' d K H G U Γ Y A φ e χ Z V):=by
    let W:= Tx; obtain ⟨w,h,_⟩:=Array_v L' d K H G U Γ Y A φ p' hF; have ht:= (beck W hF.favorable hF.sturdy h hF.bays.1 (zero_lt_one.trans_le hF.strength) χ V).1.norm
    apply Summable.of_norm_bounded ht; intro i; unfold game Play.Camp.port; split; next ht=>split; · exact le_rfl
                                                                                            rw [norm_zero]; exact norm_nonneg _
    rw [norm_zero]; exact norm_nonneg _
local notation "Of"=> game L' d K H G U Γ Y A φ e χ
-- adapt arguments order (Z after χ?) check
noncomputable def mage (Z:Finset I)(V:Grid c):= T0 (∑' i, (Of) Z V i)
local notation "F!"=> mage L' d K H G U Γ Y A φ e χ
lemma absent : F! ∅ V=0:=by unfold mage game; simp
-- Build array taking pre-T mask weights. Need represent as visible log for EACH smaller T support Σ.
include hR
lemma respectful (i:Clusters (Tx).Bright)(Z:Finset I): (withdraw N ((S').ratio.parent∘ A) φ) (Of Z V i)∈ VaultP K1 q₀ Z:=by
    unfold game; split
    next hz=>
        rw [← hz.2]; unfold Play.Camp.port; split
        next hv=>
           have hp:=hF.favorable; let Tx':= Tx; have hx:= hR -- include 
           change T0 ((Tx).honest _ _ _)∈ _; unfold Fleet.honest; by_cases hm:Healthy (Pressure.temp τ) (seatP (Tx).lightF i) V
           · rw [masked_eq _ _ _ _ hm]; exact (swingM N lk φ q₀ Tx' (Oi) hx (zero_lt_one.trans_le hF.strength) χ V i).shows
           rw [masked_ne _ _ _ _ hm,map_zero]; apply Submodule.zero_mem
        rw [map_zero]; exact Submodule.zero_mem _
    rw [map_zero]; exact Submodule.zero_mem _
lemma respectfulSum : F! Z V∈ VaultP K1 q₀ Z:=by
    unfold mage; let C:= LinearMap.toContinuousLinearMap ((T0).toLinearMap) -- Typo
    change C (∑' i,(Of) Z V i)∈ _; rw [C.map_tsum (gate_sum L' d K H G U Γ Y A φ e χ V p' hF Z)]; apply polite_tsum; intro i; exact respectful L' d K H G U Γ Y A φ e χ V p' hF hR i Z
omit hR hF
lemma swingD (i:Clusters (Tx).Bright) (Jx:∀ j:Option (Fin i.fst),Ip) (hh:∀ j,(i.2 j).val=badge (Zⁱ) (S') _ (Jx j)): (sM) i= Finset.univ.biUnion fun j=> Y.markers (Jx j).val:=by
    unfold swingE; have hf j:deathT (Oi) (i.2 j).val= Y.markers (Jx j).val:=by rw [hh]; unfold deathT; rw [show (badge ..).toRight= {Sum.inl (Jx j)} from ?_,singleton_biUnion]; rfl; ext; simp [badge]
    simp_rw [hf]
local notation "PQV" x=> Play.Camp.port H Z' Zⁱ Y A φ inH (Pe (fled Y e x)) χ V
lemma aligns (i:Clusters (Tx).Bright)(W:Finset I)(hh:Z⊆W)(hx:(sM) i ⊆ Z): (PQV W) i= (PQV Z) i:=by
   unfold Camp.port; apply if_congr _ rfl rfl; constructor
   · intro hv; choose Jx h hD using hv; have hV:=swingD L' d K H G U Γ Y A φ _ _ hD; intro j; refine ⟨Jx j,(fun t ht=> ?_),hD j⟩; have hb:=h j ht; rcases t with t|t|t
     · exact inl_mem_disjSum.mpr (inl_mem_disjSum.mp hb)
     · refine inr_mem_disjSum.mpr (inl_mem_disjSum.mpr (mem_filter.mpr ⟨(mem_filter.mp (inl_mem_disjSum.mp (inr_mem_disjSum.mp hb))).1,fun i' hi=> hx ?_⟩))
       rw [hV]; exact mem_biUnion.mpr ⟨_,mem_univ j,mem_union_left _ (mem_biUnion.mpr ⟨t,mem_toLeft.mpr (mem_toRight.mpr ht),hi⟩)⟩
     exact inr_mem_disjSum.mpr (inr_mem_disjSum.mpr (inr_mem_disjSum.mp (inr_mem_disjSum.mp hb)))
   intro hv j; obtain ⟨w,hp,ht⟩:= hv j; refine ⟨_, hp.trans (disjSum_mono (Subset.refl _) (disjSum_mono ?_ (Subset.refl _))),ht⟩; intro i hi; obtain ⟨h,hv⟩:= mem_filter.mp hi; exact mem_filter.mpr ⟨h,hv.trans hh⟩
include hE hF
lemma scalesV (i:Clusters (Tx).Bright) : (PQV Z) i=∑ W∈ Z.powerset.erase ∅,(Of) W V i:=by
    have hz:∀ j∈leftE (Pe (fled Y e Z)), (Y.spine j).Nonempty:= fun j hj=> by rw [pinX] at hj; exact hE _ (mem_filter.mp hj).1
    let W'':= (sM) i; let P v:=(Of) v V i; let Q:=Z.powerset.erase ∅
    by_cases h:W''∈ Q
    · rw [Finset.sum_eq_single_of_mem _ h]; unfold game; rw [if_pos ⟨Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_erase h),rfl⟩]; exact aligns L' d K H G U Γ Y A φ e W'' χ V i Z (mem_powerset.mp (mem_of_mem_erase h)) (Subset.refl _)
      intro b hv hb; exact if_neg (fun h=> hb h.2.symm)
    · have hg b (hv:b∈Q): (Of) b V i=0:=by unfold game; exact if_neg (fun h':b.Nonempty ∧ W''=b=> h ((show W''=b from h'.2).symm ▸ hv))
      rw [Finset.sum_eq_zero hg]
      by_contra hG
      unfold Play.Camp.port at hG; split at hG; swap; · exact hG rfl
      next ht=>
         apply h; choose w hP hW using ht
         have hs := swingD L' d K H G U Γ Y A φ i w hW
         have hv k : leftE (w k).val ⊆ fled Y e Z:=by
            intro z hz; exact inl_mem_disjSum.mp (inr_mem_disjSum.mp (hP k (mem_toRight.mp (mem_toLeft.mp hz))))
         have hD j : Burke P₀ (Z') (w j).val:=by
            by_contra hz
            apply hG; change (Tx).honest χ V i=0; rw [Fleet.phoenix (Tx) χ V hF.favorable]; unfold GasP.termP; rw [prod_eq_zero (mem_univ j) (show (Tx).dawnV χ V (i.snd j)=0 from ?_), smul_zero,smul_zero]
            unfold dawnV; rw [hW]; exact ineligible H (Z') Zⁱ Y A φ inH _ χ V _ (hP j) hz (pinK ..) hF.property
         unfold W'' Q; rw [hs]; refine mem_erase.mpr ⟨Finset.Nonempty.ne_empty (?_),mem_powerset.mpr (?_)⟩
         · let j : Option (Fin i.fst):=none; obtain ⟨b,hb⟩:= TabletV.lush (Z') (w j).val (w j).2.1 (TabletV.spentP _ _ (hP j) (pinK ..)) (hD j); obtain ⟨u,hu⟩:=hE b (mem_filter.mp (hv _ hb)).1; exact ⟨_,mem_biUnion.mpr ⟨j,mem_univ _,mem_union_left _ (mem_biUnion.mpr ⟨_,hb,hu⟩)⟩⟩
         intro p hp; obtain ⟨j,hj,hp⟩:=mem_biUnion.mp hp; have hh:spent (w j).val=∅:=TabletV.spentP _ _ (hP j) (pinK ..); change p∈ Y.markers (w j).val at hp; rw [markers,hh,biUnion_empty,union_empty] at hp; obtain ⟨k,hk,hp⟩:=mem_biUnion.mp hp; exact (mem_filter.mp (hv _ hk)).2 hp
-- exp identity.Telescope actual. Issue payload of Fp.RO.Parent.Clm
lemma wall : NormedSpace.exp (∑ v∈Z.powerset.erase ∅, F! v V)= T0 (NormedSpace.exp (∑' i:Clusters (Tx).Bright,(PQV Z) i)):=by
    have h v := gate_sum L' d K H G U Γ Y A φ e χ V p' hF v
    let P:= (T0).toLinearMap.toContinuousLinearMap; rw [NormedSpace.map_exp (T0) P.continuous]; apply congr_arg; simp_rw [scalesV L' d K H G U Γ Y A φ e Z χ V p' hF hE]; rw [Summable.tsum_finsetSum (fun i _=>h i),map_sum]; rfl
end Grove
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.Grove.wall
#print axioms YM.MassiveQCD.Apron.Grove.respectfulSum
