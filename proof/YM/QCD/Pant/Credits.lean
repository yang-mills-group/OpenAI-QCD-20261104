import YM.QCD.Pant.Waist
/-! # Rain off flanks. Masks conserved. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut
variable {K: EvenA c N→+*EvenA c N}
section hue
-- fuel any Y.sings no frame motion at z=1 OFF Domain. supplies
lemma integralW (hg:Y.sings (fun _=>1) K)(hp: Bijective K) (j:Pipe.Clump S ι) (χ:Chi)(V:Grid c): K (Y.brisk j χ V)=Y.brisk j χ V:=by
    have he F (X:Coat T F) : K (Y.bandL j X)=Y.bandL j X:=by
       unfold bandL; split
       swap; · exact map_zero _
       unfold choiceS; rw [eSM K hg.cont,map_sum]; apply congr_arg; refine sum_congr rfl fun i _=> ?_; unfold Fleet.lows; rw [eVoc K hg.cont hp]; apply integral_congr_ae; filter_upwards with y
       rw [eVoc K hg.cont hp]; apply integral_congr_ae; filter_upwards with z; unfold regards; dsimp only; rw [eSM K hg.cont,eSM K hg.cont,map_prod]; apply congr_arg; apply congr_arg; refine prod_congr rfl fun i _=>?_ ; unfold muscle; dsimp only; rw [eSM K hg.cont]; apply congr_arg
       have hh (X:Grid f) (Y':Grid c): K (Y.works i X Y')=Y.works i X Y':=by have hv : K (Y.works i (gauge (fun _=>1) X) (gauge (fun _=>1) Y'))=Y.works i X Y':=hg.verse i X Y'; rwa [presenceP,presenceP] at hv
       exact hh ..
    unfold brisk choiceS; rw [eSM K hg.cont,map_sum]; apply congr_arg; apply sum_congr rfl; exact fun i _=> he _ _
lemma furnaceW (hg:Y.sings (fun _=>1) K)(hp: Bijective K) (χ:Chi)(V:Grid c) (j:Clusters Y.Bright): K (Y.furnace χ V j)=Y.furnace χ V j:=by unfold furnace termP; rw [eSM K hg.cont,eSM K hg.cont,map_prod]; apply congr_arg; apply congr_arg; exact prod_congr rfl fun i _=> integralW Y hg hp _ _ _
lemma marchW {w:Site c →su.El} (hg:Y.sings w K)(hp:Y.Famous)(χ:Chi)(V:Grid c)(ht:Summable (fun i=>Y.honest χ (gauge w V) i)) (j:Y.Wort):K (Y.mission χ (gauge w V) j)=Y.mission χ V j:=by
    unfold Fleet.mission
    let f₁:=Y.duskV χ (Lattice.gauge w V); let g₁:=Y.duskV χ V; let f₂:= Y.dawnV χ (Lattice.gauge w V); let g₂:=Y.dawnV χ V
    have hS: Summable (termP (blocked Y.lightF) f₂):=ht.congr (fun i=> phoenix Y χ _ hp i)
    have he:=railL (x:=Equiv.refl _) (p:=Equiv.refl _) (p':=Equiv.refl _) (s:=Y.broad) (r:=Y.lightF) (q:=Y.invD) (fun _=> Finset.image_id.symm) (fun _=>Finset.image_id.symm) (fun _=>Finset.image_id.symm) hg.cont (fun i=>show K (f₁ i)=g₁ i from Fleet.factor Y hg _ hp ..) (fun i=>show K (f₂ i)=g₂ i from Fleet.factor Y hg _ hp ..) hS (RG.flags (Pressure.temp τ) (Lattice.gauge w V)) j
    refine he.trans ?_; congr 1
    · simp
    simp [horse]
end hue
open PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange AnalyticBridge.GaussianFieldAlignment Locations Channels
section sym
variable {p:Strut c}{π:R.activities.Moves p.1 (S.ratio.embed p.2)}{Ω:Equiv.Perm ι}
variable (h:Y.Marches (s:=p.1) (b:=p.2) π Ω K)
set_option quotPrecheck false
local notation "r"=> rune π Ω
local notation "F'"=> Classical.choice (Tree.select S.ratio S.patch.odd_side)
include h -- flag remainder
lemma crownB (i:Pipe.Clump S ι): (Y.Given i↔ Y.Given (r i)) ∧ (roster (r i).toLeft).flags=(roster i.toLeft).flags.image (act p):=by
   have hv:= daring h (F') (F') i -- sig
   obtain ⟨hA,hB,hC⟩:=hv
   refine ⟨and_congr ?_ (and_congr hB hA),?_⟩
   · rw [hC]; simp
   let Z:= r i; have hh:roster i.toLeft= Locations.book p.1 p.2 (roster Z.toLeft):=by unfold Z; rw [legL]; exact PhysicalNext.Repeat.Turn.mark R π i.toLeft
   change _=_; rw [hh]; exact (display (act p) _ _).2 (fun j=> atF ..)
lemma shineZ (i:Pipe.Clump S ι): (Given Y i∧ (roster i.toLeft).flags=∅ ↔ Given Y (r i)∧ (roster (r i).toLeft).flags=∅) ∧
  (Given Y i∧(roster i.toLeft).flags.Nonempty ↔ Given Y (r i)∧(roster (r i).toLeft).flags.Nonempty):=by
    rw [(crownB Y h i).1,(crownB Y h i).2]; simp
noncomputable def ebony : Equiv.Perm Y.Dark:= Equiv.subtypeEquiv r (fun i=> (shineZ Y h i).2)
noncomputable def adawn : Equiv.Perm Y.Bright:= Equiv.subtypeEquiv r (fun i=> (shineZ Y h i).1)
lemma mermaid : Got Y.broad (ebony Y h) (act p) :=fun i=>(daring h F' F' i.1).2.2
lemma mayD : Got Y.lightF (adawn Y h) (act p):=fun i=>(daring h F' F' i.1).2.2
lemma seedD : Got Y.invD (ebony Y h) (act p):=fun i=>(crownB Y h _).2
noncomputable def ebonyJ: Equiv.Perm Y.Faber:= Equiv.subtypeEquiv ((horse (ebony Y h) (act p)).finsetCongr) (friend (mermaid Y h))
lemma waistF (hp:Y.Famous)(χ: Chi)(V:Grid c)(ht: Summable (honest Y χ (sky p V))) (j:Y.Wort): K (Y.mission χ (sky p V) j)= Y.mission χ V ((horse (ebony Y h) (act p)).finsetCongr j):=by
    have hh:= railL (mermaid Y h) (mayD Y h) (seedD Y h) h.cont (fun i=> show K (duskV Y χ (sky p V) i)= duskV Y χ V (ebony Y h i) from godet h i.1 hp ..) (fun i=> show K (dawnV Y χ (sky p V) i)=dawnV Y χ V (adawn Y h i) from godet h i.1 hp ..) (ht.congr fun i=>phoenix Y χ _ hp i) (RG.flags (Pressure.temp τ) (sky p V)) j
    refine hh.trans ?_; unfold mission; congr 1; exact Work.H03.flags_send ..
lemma gistE (hp:Y.Famous)(χ:Chi)(V:Grid c)(j:Clusters Y.Bright): K (Y.honest χ (sky p V) j)= Y.honest χ V (Patron.pack (adawn Y h) j):=by
    rw [phoenix Y χ _ hp,phoenix Y χ _ hp]; exact spry (mayD Y h) h.cont (fun i=>godet h i.1 hp ..) j
end sym
end YM.QCD.Patron
