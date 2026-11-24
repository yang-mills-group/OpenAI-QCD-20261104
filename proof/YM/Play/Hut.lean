import YM.Play.Camp
import YM.QCD.House.Plenary
set_option autoImplicit false
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
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
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
section optics
-- call generic, no counts
variable (V:Fleet H κ (ample N I))
variable {uw: Reserve S→κ→ℝ} {w:κ→ℝ}{cost:Costs}{α φ:ℝ}
local notation "Dk"=> V.dawnV χ U
lemma flame (L:Finset V.Bright) (hV:V.Famous) (ht: V.Leaps uw cost w φ)(hh:Corner Q (radiusB τ) cost α)(hs:1≤φ) (F:Clusters V.Bright→ EvenA c (ample N I))(hf:∀ i,(∀ j,i.2 j∈L) → F i = V.honest χ U i) (hg:∀ i, (¬∀ j,i.2 j∈L) → F i=0):
   NormedSpace.exp (∑' i:Clusters V.Bright, F i)=∑ i∈Camp.cliques V.lightF L, ∏ j∈i,(Dk) j:=by
    let H:=V.lightF; let T:= Camp.cliques H L; let y i:= if i ∈ L then (Dk) i else 0
    have hp : Ready H (radiusB τ) (fun i=>‖y i‖) (α+1) (apple cost) 1 (1/2):=by
       refine foyer (fun i=> norm_nonneg _) (Fleet.ceremony V ht (add_nonneg hh.exp zero_le_one) hh.used zero_lt_one hh.directs hh.adds (by norm_num)) ?_; intro i; unfold y; split
       · exact (Loom.tore _ hs).trans (Fleet.localP V ht χ U i.val)
       rw [norm_zero]; exact (norm_nonneg _).trans (Fleet.localP V ht χ U i.val)
    have he:= price_log (blocked H) y ⟨fun i=> .inl rfl,fun _ _=>blocked_back H⟩ H (radiusB τ) (literal_test H (fun i=> i.2.1.1)) (add_nonneg hh.exp zero_le_one) hp
    have hf i : F i= GasP.termP (blocked H) y i:=by
        by_cases ht:∀ j,i.2 j∈L
        · rw [hf _ ht,phoenix V χ U hV]; unfold GasP.termP; apply congr_arg; apply congr_arg; exact prod_congr rfl (fun j _=> (if_pos (ht j)).symm)
        rw [hg _ ht]; symm; push Not at ht; obtain ⟨j,hj⟩:=ht; unfold GasP.termP; rw [prod_eq_zero (mem_univ j) (show y (i.2 j)=0 from if_neg hj),smul_zero,smul_zero]
    simp_rw [hf]; rw [show NormedSpace.exp (∑' i,termP (blocked H) y i)=_ from he.2.2]; unfold GasP.totalP; rw [tsum_eq_sum (s:=T)]; refine sum_congr rfl fun i hi=>?_
    · obtain ⟨hv,hQ⟩:=mem_filter.mp hi; unfold GasP.valueP; rw [if_pos ((GasP.close _ H _).2 hQ)]; exact prod_congr rfl (fun j hj=> if_pos (mem_powerset.mp hv hj))
    intro i hi; unfold GasP.valueP; split
    next h₀ =>
       have hz: ¬i∈ L.powerset:= fun hx=> hi (mem_filter.mpr ⟨hx,(GasP.close _ H _).1 h₀⟩)
       rw [mem_powerset] at hz; obtain ⟨j,hj,hz⟩:=Finset.not_subset.mp hz; exact prod_eq_zero hj (show y j=0 from if_neg hz)
    rfl
end optics
variable (hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)
set_option quotPrecheck false
local notation "H'"=> student H G M X z a Y p hk hw hs he
local notation "Zs"=> campus H G M X z a Y p hk hw hs he
local notation "Ip"=> ↥(plume P₀ G M p)
local notation "Cv"=> month (P₀:=P₀) M G p
-- ignored Burke bits pull to criterion only, no tests assumed for purchase
lemma ineligible (i:V') (hv: i.val⊆p) (hh: ¬ Burke P₀ G i.val) (he:spent p=∅)(hw:X.Wave O.threshold q' z): (Tx).vF (badge M S κ i) χ U=0:=by
   let Qx:= Tx; let T' := badge M S κ i
   unfold vF
   have hQ (F:Tree.Forest S.ratio) (Z:Coat T F): ((Tx).suitcase F).shootsP Z T'=0:=by
     unfold shootsP; split
     next =>
       let x:= planted Z T'.toLeft
       let g:= ((Tx).suitcase F).capacityP T' (own T'.toLeft)
       have ht (Y':Coat T F)(w:Air f su) : (Tx).coming (.inl i) Y' w=0:=by
           let V:= Y'.input (Y'.liftA β w); have hg:X.hue O.threshold G i.val V=0:=by_contra fun h=> hh (TabletV.vibrant X G hw _ _ (spentP _ _ hv he) h)
           change (Tx).riseP Y' w (.inl i) • (δ⁻¹ ^ _ • Β (X.hue O.threshold G i.val V))=_; rw [hg,map_zero,smul_zero,smul_zero]
       have hx (j:S.Choices): call (x.taggedL j) g=0:=by
          unfold call; refine (integral_congr_ae ?_).trans (integral_zero ..); exact ae_of_all _ fun l=> by unfold g Pipe.capacityP; dsimp only [T',badge]; rw [show ((Tx).suitcase F).averageP _ _ _=0 from prod_eq_zero (mem_toRight.mpr (mem_singleton_self (Sum.inr (α:=Head S) (Sum.inl i)))) (ht _ _),smul_zero]
       change (Fintype.card S.Choices:ℝ)⁻¹ • ∑ j:S.Choices, call (x.taggedL j) g=0; simp_rw [hx,sum_const_zero,smul_zero]
     rfl
   change choiceS (fun j:Reserve S=> ((Tx).suitcase (allot j)).shootsP _ T')=_; simp_rw [hQ]; rw [choiceS,sum_const_zero,smul_zero]
-- characteristic
abbrev front (M:Fj D E J→Support c) (S:StepData c f)(κ:Type) (p: Finset (Fj D E J))(s:Clump S (Wound M⊕κ)):Prop:=∃ (i:Wound M), i.val⊆p∧s=badge M S κ i
def port (_p:Finset (Fj D E J))(χ:Chi)(U:Grid c)(i:Clusters (Tx).Bright):= if ∀ j,front M S κ _p (i.2 j).val then (Tx).honest χ U i else 0
include hw hk hs he
lemma studious (i:Clusters (Tx).Bright)(hV:(Tx).Famous): port H G M X z a Y p χ U i=(if ∀ j,i.2 j∈Zs then (Tx).honest χ U i else 0):=by
   unfold port; split_ifs with hv ht ht; exact rfl
   · push Not at ht; obtain ⟨j,hj⟩:=ht; obtain ⟨k,hk₁,hVq⟩:=hv j; have hz:¬ Burke P₀ G k.val:= by
        intro hh; let x:Ip:= ⟨k.val,mem_filter.mpr ⟨mem_powerset.mpr hk₁,k.property, hh⟩⟩; apply hj; exact mem_image.mpr ⟨x, mem_univ _, Subtype.ext (Eq.trans (congr_arg (badge M S κ) (show child G M p x = k from Subtype.ext rfl)) hVq.symm)⟩
     rw [phoenix (Tx) χ U hV]; unfold GasP.termP; rw [prod_eq_zero (mem_univ j) (show (Tx).dawnV χ U (i.2 j)=0 from by unfold Fleet.dawnV; rw [hVq]; exact ineligible H G M X z a Y p χ U _ hk₁ hz he hw),smul_zero,smul_zero]
   · exfalso; apply hv; intro j; obtain ⟨k,hk,r⟩:= mem_image.mp (ht j); refine ⟨child G M p k, mem_powerset.mp (mem_filter.mp k.2).1,?_⟩; rw [← r]; rfl
   rfl
variable {uw: Reserve S→(Wound M⊕κ)→ℝ} {w:(Wound M⊕κ)→ℝ}{cost:Costs}{α φ:ℝ}
set_option maxHeartbeats 550000 in
lemma minion (hV:(Tx).Famous) (ht: (Tx).Leaps uw cost w φ)(hh:Corner Q (radiusB τ) cost α)(hq:1≤φ):
    NormedSpace.exp (∑' i:Clusters (Tx).Bright, port H G M X z a Y p χ U i) = ∑ i∈month (P₀:=P₀) M G p, ∏ j∈i,(Tx).vF (badge M S κ (child G M p j)) χ U:=by
    let pV:= Zs; have hv:= studious H G M X z a Y hw hk p χ U hs he; refine Eq.trans (flame H χ U (Tx) Zs hV ht hh hq _ (fun i hh=> (hv i hV).trans (if_pos hh)) (fun i hh=> (hv i hV).trans (if_neg hh))) ?_
    
    rw [clinics H G M X z a Y hw hk p hs he,sum_image]
    have hl:= pupil H G M X z a Y hw hk p hs he; refine sum_congr rfl fun i _=> ?_; rw [prod_image hl.injOn]; rfl
    exact (Finset.image_injective (pupil H G M X z a Y hw hk p hs he)).injOn
end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.minion
