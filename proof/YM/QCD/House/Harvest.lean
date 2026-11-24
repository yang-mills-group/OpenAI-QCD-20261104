import YM.QCD.House.Auxiliary
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Villa
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Cove Leaf Lat Creek Loom
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass Sway OrbitG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {Y:StepData c f} {η p h z a a' t v u u' q:ℝ} {D E J:Type}[Countable E][Countable J][Fintype D]
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
local notation "B" => radiusB τ
open Sway OrbitG Strut Revolve
variable {W' :ℕ→Atom su 2}{J':Plan k}
variable (O:Flight j k)(K: KernelChoices)(d:f.val=c.val*O.L.val)
set_option quotPrecheck false
local notation "S"=> (O.visit K d).ratio
variable {T : Tube su (O.visit K d)}
variable {X:Grid f→Sheet f} (H:Cash W τ μ O.L Q o C T (trimP T R δ β b))(G:Sun O c f d η h z a a' m X) (U :Swathe O d X W' J' h η a u v i)
variable {Γ: Land c (Site c) (Site c)}{D':Pays c (Site c) (Site c)}
variable (Y': Rise f N E J)
local notation "Z'"=> tableau O d K Y' H G U Γ
lemma validH
   (hs:0<radiusB τ): Fleet.Feasible (Z') :=by
   let V:= G.equip N B; let X:= roof V Y' 30 B; let Z:= tableau O d K Y' H G U Γ
   constructor
   rintro (i|i|i) U' x hp
   · -- Wound i .spark. extract parent E or K
     have hv: hue V Y' R.threshold i.1 U' ≠0:=fun ht=>hp (by exact (congr_arg (δ⁻¹ ^ budget Y' i.1 • ·) ht).trans (smul_zero _))
     have he: (leftE i.1).Nonempty∨ (spent i.1).Nonempty:=by
        by_contra! h
        apply hv; exact Cove.nightly V Y' i.1 i.2.1 h.1 h.2 U'
     have hx j: Cove.native V Y' j⊆ Cove.brim V Y' j:=halo_subset ..
     have ht j: (Cove.native V Y' j).image (S).parent⊆ X j:= (Finset.image_subset_image (hx _)).trans ((roofs V Y' 30 B (le_refl _) hs).1.budget _)
     obtain ⟨j,hj⟩|⟨j,hj⟩:=he
     · let w:=(Y'.row j); refine  Finset.Nonempty.mono ?_ ((Finset.Nonempty.image (⟨w.site,w.anchor⟩ : w.support.Nonempty) ((S).parent)))
       have he: Sum.inr (Sum.inl j)∈i.1:=mem_toRight.mp (mem_toLeft.mp hj)
       exact (ht (.inr (.inl j))).trans (subset_biUnion_of_mem X he)
     let W:=Y'.front j; have he: Sum.inr (Sum.inr j) ∈ i.1:= mem_toRight.mp (mem_toRight.mp hj)
     exact Finset.Nonempty.mono ((ht (.inr (.inr j))).trans (subset_biUnion_of_mem X he)) (Finset.Nonempty.image (W.alive.mono W.part) _)
   · refine Finset.Nonempty.mono (halo_subset ..) ?_
     exact Finset.Nonempty.mono (Loom.marks i _ _) (halo_subset (6*B) {Loom.siteH i S} |> fun h=>Nonempty.mono h (singleton_nonempty _))
   refine Finset.Nonempty.mono (halo_subset ..) ?_
   exact Finset.Nonempty.mono (Loom.seaP i B S) (Finset.Nonempty.mono (halo_subset (6*B) {i.1}) (singleton_nonempty _))
variable {η' θ :ℝ}
lemma loan (hw:∀ F, Within O d K Y' H G U θ η' F Γ): let b:=Pipe.unitsP Q O.L μ β τ C (shiftCost O.L τ (romp O.L)) (demandQ O.L θ τ)
         ∃ w,Fleet.Leaps (Z') w b (fun _=>0) η':=by
   intro b; let Z:= tableau O d K Y' H G U Γ; choose w h hb hL using fun (i: PhysicalNext.Repeat.Greenbelt.Reserve (O.visit K d))=> (hw (PhysicalNext.Repeat.Greenbelt.allot i)).2.2.1
   exact ⟨w,fun i=>⟨h i,fun p V χ=>hb i (PhysicalNext.Repeat.Greenbelt.prism T τ χ o.K V (PhysicalNext.Repeat.Greenbelt.allot i)) rfl rfl _⟩⟩ -- Binder signature args orientation Y
open PhysicalNext.Repeat.Greenbelt Territory
open scoped PhysicalNext.Repeat.Greenbelt
lemma star_push (hw:∀ F, Within O d K Y' H G U θ η' F Γ)(F:Tree.Forest (Flight.visit O K d).ratio)(V:Grid c)(χ:Chi) :
    let P:=tableau O d K Y' H G U Γ
    let Z:= prism T τ χ o.K V F
    HasSum (fun i=> (X 1).det^N • (Cove.light _ (Matter.overhead Z (trimP T R δ β b) Q.table • P.emergingF i χ V)*gauss (Lat.copies N (wood J' 0 O.land V)))) ((O.visit K d).push β (Emitter O d K Y' T δ β b R W' X) V):=by
    intro P' Z
    let T':= trimP T R δ β b
    let Y (s:Reserve (O.visit K d)):= prism T τ χ o.K V (allot s)
    let C:=gauss (Lat.copies N (wood J' 0 O.land V)); let g s:= Pipe.drawP (P'.suitcase (allot s)) (Y s); let A:= (X 1).det^N; let h:= Matter.overhead Z T' Q.table; let p:=(O.visit K d).push β (Emitter O d K Y' T δ β b R W' X) V
    have hx s: Matter.overhead (Y s) T' Q.table=h:= TreeColor.overhead_eq (Y s) Z rfl H.laws.intake.ready rfl Q.table T'
    have hw' s : HasSum (fun i=> A • (Cove.light _ (h • g s i)*C)) p:=by rw [← hx s]; exact (hw (allot s)).2.2.2 (Y s) rfl rfl
    have he i: A • (Cove.light _ (h • P'.emergingF i χ V)*C)= (Fintype.card (Reserve (O.visit K d)):ℝ)⁻¹ • ∑ j:Reserve (O.visit K d), A • (Cove.light _ (h • g j i)*C):=by
       rw [Fleet.ensemble P' V χ (hw F).1]; let l:= Loom.Y'' C A; have hh u:A • (Cove.light _ u*C)=l u:=rfl
       simp only [hh,choiceS,map_sum,map_smul]; rw [smul_comm]; simp_rw [Finset.smul_sum]; rfl
    change HasSum (fun i=>A • (Cove.light _ (h • _)*C)) p; simp_rw [he]
    letI:Nonempty (Tree.Forest S):=Tree.select S O.odd
    suffices hx: (Fintype.card (Reserve (O.visit K d)):ℝ)⁻¹ • (∑ _i:Reserve (O.visit K d),p)=p by nth_rw 1 [← hx]; exact Fleet.hS _ _ _ hw'
    simp [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
end YM.QCD.Villa
