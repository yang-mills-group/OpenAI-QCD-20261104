import YM.QCD.House.Jamb

/-! # Forest purchases and wash budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
local notation "V'"=> prism T τ
open Art
namespace GlintV
open Pipe
variable (χ:Chi)(V:Grid c)
local notation "PS"=>Matter.planted
local notation "κv" i=>V' χ o.K V (allot i)
local notation "pT" X:arg=> PS X ∅
lemma grouped (h:Y.Famous)(s:Finset I)(hs:Y.shellF.legal s):
   (∏ i∈s,Y.vF i χ V)=choiceS fun i:Reserve S=> ∏ j∈s,(Y.suitcase (allot i)).shootsP (κv i) j:=by
   letI : Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
   simp_rw [← prod_coe_sort s]; symm
   let u (j:↥s)(i:Reserve S):= (Y.suitcase (allot i)).shootsP (κv i) j.val
   refine Beam.fairT («I»:=Site c) (A:=Tree.Forest S.ratio) (Y:=↥s) (inferInstanceAs (Fintype (Reserve S))) u (Y.fullA ∘ fun j:↥s=>j.val) ?_ ?_
   · intro i _ j _ hn; exact hs.2 i.property j.property (fun h=> hn (Subtype.ext h))
   intro j r v hh; apply spacial Y j.val h (κv r) (κv v) rfl rfl rfl rfl rfl (fun _ _ _=>rfl) rfl
   intro i hi; change (r (S.ratio.parent i)).up i=(v (S.ratio.parent i)).up i; rw [hh _ hi]
-- equality as integrated on common tags and orientation F for pure motions
lemma pureP (x:Finset I) (h:Y.Famous)(hs:Y.shellF.legal x)(he:∀ i∈x,Y.shellF.born i)(hh:∀ i∈x,(i: Finset (Piece S ι)).toLeft=∅)(hv:∀ i∈x,Healthy (Pressure.temp τ) (Y.fullA i) V) : (∏ i∈x,Y.vF i χ V)=choiceS fun i:Reserve S=> Beam.draws (Matter.planted (prism T τ χ o.K V (allot i)) (∅:Finset (Head S))) ((Y.suitcase (allot i)).capacityP (x.biUnion id) ∅):=by
   rw [grouped Y χ V h x hs]; apply congr_arg choiceS; funext i
   let p:=(Y.suitcase (allot i)); have hp:=p.transmitted (pT (κv i)) ∅ (Fleet.forwarded _ _ h) x hs rfl rfl (planted_valid ..); refine Eq.trans (b:=∏ j∈x,draws (pT (κv i)) (p.capacityP j ∅)) ?_ hp.symm
   apply prod_congr rfl; intro j hj; unfold Pipe.shootsP
   have hl: RG.flags (Pressure.temp τ) V ∩ Y.fullA j=(roster j.toLeft).flags:=by
       rw [hh j hj]; rw [inter_comm,Finset.disjoint_iff_inter_eq_empty.mp (hv _ hj)]
       ext i; simp [roster, Packets.store]
   change (if Ac.Spark Y.shellF.gP _ ∧ Y.shellF.born _ ∧ RG.flags (Pressure.temp τ) V∩Y.fullA j=(roster j.toLeft).flags then _ else _)=_
   rw [if_pos ⟨(hs.1 j hj),he j hj,hl⟩,hh j hj, show own (∅:Finset (Head S))=∅ from ?_] -- script
   ext; simp [Matter.own]
lemma pure_term (F:Tree.Forest S.ratio)(X:C' F) (s:Finset ι)(k:Finset ℕ) (w:Air f su): (Y.suitcase F).capacityP (Finset.disjSum (∅:Finset (Head S)) s) k X w= ∏ j∈s,Y.coming j X w:=by
    unfold capacityP; rw [Finset.toLeft_disjSum,Finset.toRight_disjSum];
    unfold Coat.term; rw [prod_empty,one_smul]; rfl
end GlintV
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.GlintV.pureP
#print axioms YM.QCD.Loom.Fleet.GlintV.pure_term
