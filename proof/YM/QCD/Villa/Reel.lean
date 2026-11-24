import YM.QCD.Villa.Music

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
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
variable {s:Signed}{b:Site c}(v:R.activities.Moves s (S.ratio.embed b))(w:Equiv.Perm ι)(K:EvenA c N →+* EvenA c N)
-- direction standard: f(s*p)= f(pull s v)(old). supply co-transform
structure Marches (v:R.activities.Moves s (S.ratio.embed b))(w:Equiv.Perm ι)(K:EvenA c N→+* EvenA c N):Prop where
 cont : Continuous K
 days i j: j∈ Y.limit i↔ v.kp j∈ Y.limit (w i)
 paths i j:j∈Y.ground i↔ affine s b j∈Y.ground (w i)
 glasses i j:j∈Y.window i↔ affine s b j∈Y.window (w i)
 groups i j :Y.compat i j↔ Y.compat (w i) (w j)
 turns i x y : Y.works (w i) x y= K (Y.works i (pull s (S.ratio.embed b) x) (pull s b y))
variable {Y v w K}
abbrev rune (v:R.activities.Moves s (S.ratio.embed b)) (w:Equiv.Perm ι):Equiv.Perm (Pipe.Clump S ι):=(Equiv.sumCongr (badge R v) w).finsetCongr
lemma legL (i:I) : (rune v w i).toLeft=caravan R v i.toLeft:=by ext j; obtain ⟨j,rfl⟩:= (badge R v).surjective j; simp [rune,caravan]
lemma legR (i:I): (rune v w i).toRight=w.finsetCongr i.toRight:=by ext j; obtain ⟨j,rfl⟩:= w.surjective j; simp [rune]
variable (h:Y.Marches v w K)
include h
local notation "Zs"=> Locations.forest s b F
lemma protection (A:Forest S.ratio)(i:Pipe.Piece S ι)(j:Site c) : j∈ (Y.suitcase A).gP i ↔ StepData.sendSites s b j∈ (Y.suitcase A).gP ((Equiv.sumCongr (badge R v) w) i):=by
   cases i
   next i=> exact (PhysicalNext.Repeat.Turn.display (StepData.sendSites s b) _ _).1 (insignia T R v Q.halo (radiusB τ) i) j
   next i=> exact h.paths i j -- multiline
lemma daring (A B:Tree.Forest S.ratio)(u:I):
   ((Y.suitcase A).born u↔ (Y.suitcase B).born (rune v w u))∧(Ac.Spark (Y.suitcase A).gP u↔ Ac.Spark (Y.suitcase B).gP (rune v w u))∧ Y.fullA (rune v w u)=(Y.fullA u).image (affine s b):=by
   let Z:=Y.suitcase A; let f:=rune v w u; let e:=Equiv.sumCongr (badge R v) w; let p:=StepData.sendSites s b
   refine ⟨?_,PhysicalNext.Repeat.Turn.seam e p (protection h A) ((given _ _ _).1 rfl), PhysicalNext.Repeat.Turn.gains e p (protection h A) ((given _ _ _).1 rfl)⟩
   have hi : Z.eligibleP u.toRight↔ Z.eligibleP (rune v w u).toRight:=by
       rw [legR]; constructor
       · intro he i hi j hj hn; obtain ⟨i,rfl⟩:=w.surjective i; obtain ⟨j,rfl⟩:=w.surjective j
         exact (h.groups i j).1 (he (by simpa using hi) (by simpa using hj) (fun h=> hn (congr_arg _ h)))
       intro he i hi j hj hn; exact (h.groups i j).2 (he (show w i∈ w.finsetCongr _ from by simpa using hi) (show w j∈w.finsetCongr _ from by simpa using hj) (w.injective.ne hn))
   have hv : Matter.own u.toLeft= Z.filterP u.toRight↔ own f.toLeft= Z.filterP f.toRight:=by
     unfold f; rw [Finset.ext_iff, Finset.ext_iff,legL,legR]; conv_rhs=> rw [← v.kp.forall_congr_right]
     refine forall_congr' fun j=>iff_congr (PhysicalNext.Repeat.Turn.chart R v u.toLeft _) ?_ -- v binder
     unfold Pipe.filterP; simp only [mem_biUnion]; conv_rhs=> rw [← w.exists_congr_right]
     apply exists_congr; intro i; simp only [Equiv.finsetCongr_apply,mem_map_equiv,Equiv.symm_apply_apply]; exact and_congr Iff.rfl (h.days i j)
   refine and_congr ?_ (and_congr hi hv); rw [legL]; exact teams T R v Q.halo (radiusB τ) _ -- sig

lemma airsK {X : Coat T F}{X':Coat T (Locations.forest s b F)}(hp:Tuned s b X X')(Z': I)(z : Air f su)(he:X.x=τ)(hu:X.width=o.K)(hx:X.manifest)(hz:X'.manifest):
   let i:=(Y.suitcase (Locations.forest s b F)).capacityP Z' (own Z'.toLeft)
   K (i X' (exhale s b X.V S z))=(Y.suitcase F).capacityP (rune v w Z') (own (rune v w Z').toLeft) X z:=by
    have hf: ShellAccess S su X.x W X.width o.γ:=by rw [he,hu]; exact H.laws.data.access
    intro i; unfold i Pipe.capacityP; rw [eSM K h.cont]; apply congr_arg₂ (· • ·)
    · rw [legL, show own (caravan R v Z'.toLeft)= _ from (given v.kp _ _).2 (PhysicalNext.Repeat.Turn.chart R v Z'.toLeft)]; exact values (badge R v) _ _ ((given _ _ _).1 rfl) _ _ (fun j _=> commend R v H hp z he hu hx hz j (own Z'.toLeft))
    unfold Pipe.averageP; rw [map_prod,legR]; apply values w _ _ ((given _ _ _).1 rfl); intro j _
    change K (Y.coming j X' (exhale ..))= Y.coming (w j) X z; unfold coming riseP; rw [eSM K h.cont,hp.axle H.laws.intake.ready hf, hp.imposes (2*o.a) (hp.plazas (h.glasses j)),hp.completed,hp.v,h.turns] -- rewrites hp.v also outside Y works maybe break
lemma accolade {X : Coat T F}{X':Coat T (Locations.forest s b F)} (u:I)(hC:Y.Famous) (he:X.x=τ)(hz:X'.x=τ)(hv:X.width=o.K)(hv':X'.width=o.K)(hX:X.χ=X'.χ)(hT:X'.V=pull s b X.V):
    K ((Y.suitcase (Locations.forest s b F)).shootsP X' u)=(Y.suitcase F).shootsP X (rune v w u):=by
    obtain ⟨hA,hS,hZ⟩:=daring h (Locations.forest s b F) F u
    let f:= rune v w u; let A:=planted X f.toLeft; let B:=planted X' u.toLeft
    have hh: roster u.toLeft=Locations.book s b (roster f.toLeft):=by unfold f; rw [legL]; exact PhysicalNext.Repeat.Turn.mark R v u.toLeft
    unfold Pipe.shootsP; rw [hA,hS] -- eliminate with explicit, don't swap
    have hc: RG.flags (Pressure.temp X'.x) X'.V∩Y.fullA u=(roster u.toLeft).flags ↔ RG.flags (Pressure.temp X.x) X.V∩Y.fullA f=(roster f.toLeft).flags:=by
        rw [Finset.ext_iff, Finset.ext_iff]; conv_rhs=> rw [← (StepData.sendSites s b).forall_congr_right]
        rw [hh,hz.trans he.symm,hT]; refine forall_congr' fun i=>iff_congr ?_ (atF s b (roster f.toLeft) i)
        rw [mem_inter,mem_inter]; exact and_congr (toured ..) ((PhysicalNext.Repeat.Turn.display (StepData.sendSites s b) _ _).1 hZ _)
    split
    next hh'=>
       rw [if_pos ⟨hh'.1,hh'.2.1,hc.mp hh'.2.2⟩]
       unfold draws choiceS; rw [eSM K h.cont,map_sum,← Equiv.sum_comp (S.withinChoice s b).symm]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_
       have ht: Parked s b A B:=by
          refine ⟨?_,hz.trans he.symm,hT⟩
          unfold A B planted preps; dsimp only; rw [hh,hz.trans he.symm,hT]; apply congrArg (Stores.mk _ _); ext i; exact (toured s b ..).trans (atF s b A.seeds i).symm
       let Y':= B.taggedL ((S.withinChoice s b).symm i); let Z:= A.taggedL i
       have hA: Z.manifest:=planted_valid ..; have hB: Y'.manifest:=planted_valid ..; have hΨ: Parked s b Z Y':= ⟨ht.seeds,hz.trans he.symm,hT⟩
       let M:= Y.suitcase F; let N:=Y.suitcase (Locations.forest s b F)
       have hp: MeasurePreserving (fun u : F.Slice su× Air _ su => (PhysicalNext.Repeat.Turn.glide s b F u.1, exhale s b Z.V S u.2)) ((F.order su).prod Z.dice)
          (((Locations.forest s b F).order su).prod Y'.dice) := (PhysicalNext.Repeat.Turn.forest_toll s b F su).prod (hΨ.preserving H.laws.intake.ready (H.laws.data.localP F Z he hv hA).sails.fullC)
       have hN:= N.ripeP (own u.toLeft) u (Y.forwarded _ hC) Y' hz hv' hB; have hm:= M.ripeP (own f.toLeft) f (Y.forwarded _ hC) Z he hv hA
       refine vocals K h.cont hp hN.1 (envPlot hm _) (envPlot hN _) ?_
       intro i; rcases i with ⟨a,z⟩; exact airsK h ⟨⟨ht.seeds,hΨ.x,hT⟩,hX.symm,hv'.trans hv.symm,rfl,rfl⟩ u z (X:=Z.wrapY a) (X':=Y'.wrapY (PhysicalNext.Repeat.Turn.glide s b F a)) he hv hA hB
    next hz=> rw [if_neg (fun h=> hz ⟨h.1,h.2.1,hc.mpr h.2.2⟩),map_zero]
lemma godet (u:I)(h':Y.Famous)(V:Grid c)(χ:Chi):K (Y.vF u χ (pull s b V))=Y.vF (rune v w u) χ V:=by
    unfold vF choiceS; rw [eSM K h.cont,map_sum, ← Equiv.sum_comp (orbitKey s b S)]; apply congr_arg; refine Finset.sum_congr rfl (fun i _=>?_) ; dsimp only; rw [f_orbit]; exact accolade h u h' rfl rfl rfl rfl rfl rfl
end YM.QCD.Loom.Fleet
