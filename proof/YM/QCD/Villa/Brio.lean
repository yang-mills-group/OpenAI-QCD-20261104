import YM.QCD.Villa.Hedges
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pallet
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sterad

/-! # All V readability, and F ensemble -/
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
def speaking (Y:Fleet H ι N):Prop:=∀ i,Measurable (uncurry (Y.works i))
open Art Blaze.Shield Blaze
lemma glassB {X:C' F}(u:I)(h:Y.speaking)(he:X.x=τ)(hk:X.width=o.K){ℓ:Finset ℕ}{A:Type*}[MeasurableSpace A] {V:A→ Grid c}{U:A→ F.Slice su}{Z:A→ Air f su}(hw: Measurable V)(hv:Measurable U)(ht:Measurable Z) : Measurable fun i=> (Y.suitcase F).capacityP u ℓ (Art.drive X (V i) (U i)) (Z i) :=by
   have hp:ShellAccess S su X.x W X.width o.γ:= by rw [he,hk]; exact H.laws.data.access
   let f i:=Art.drive X (V i) (U i); let p i:= (f i).liftA R.beta (Z i)
   have hz: Measurable p:=Art.levitate X H.laws.intake.ready hp hw hv _ ht
   have ha: Measurable (fun i=> (f i).input (p i)):= Art.entering X hw hv hz
   have hf:Measurable fun i=> (Y.suitcase F).averageP u.toRight (f i) (Z i):=by refine Finset.measurable_fun_prod _ fun i _=>?_ ; have hg: Measurable fun z=> Y.works i ((f z).input (p z)) (V z) := (h i).comp (ha.prodMk hw); exact ((X.enforce_b (2*o.a) (X.plaza (Y.window i))).comp hz).smul hg
   have hL: Measurable fun i=> (f i).term R Q.table W o.a ℓ Q.halo (Z i) u.toLeft:= Finset.measurable_fun_prod _ fun i _=> Art.portage X (he.symm ▸ H.laws.intake) Q.table Q.table_exists hp hw hv ht ..
   exact hL.smul hf
set_option maxHeartbeats 1500000 in
lemma recordB {X:C' F}(u:I) (hp:Y.Famous)(h:Y.speaking)(he:X.x=τ)(hk:X.width=o.K): Measurable fun V=> (Y.suitcase F).shootsP (vary X V) u :=by
   let Z:=Y.suitcase F
   have hh: MeasurableSet {V: Grid c| Ac.Spark Z.gP u ∧ Z.born u ∧ RG.flags (Pressure.temp (vary X V).x) V ∩ Z.full u=(roster u.toLeft).flags}:=by
     have he : {V: Grid c| Ac.Spark Z.gP u ∧ Z.born u ∧ RG.flags (Pressure.temp (vary X V).x) V ∩ Z.full u=(roster u.toLeft).flags}=⋃ b∈ univ.filter (fun b:Support c=> Ac.Spark Z.gP u∧ Z.born u ∧ b∩Z.full u=(roster u.toLeft).flags), {V|RG.flags (Pressure.temp X.x) V=b}:=by -- edit
       ext V; simp only [Set.mem_iUnion, Set.mem_setOf_eq,mem_filter,mem_univ,true_and]; refine ⟨fun he=> ⟨_,he,rfl⟩,?_⟩; rintro ⟨b,h,rfl⟩; exact h
     rw [he]; exact MeasurableSet.iUnion fun i=> MeasurableSet.iUnion fun _=>flags_measurable_eq ..
   unfold Pipe.shootsP; refine Measurable.ite hh ?_ measurable_const
   unfold draws choiceS; refine measurable_const.smul (Finset.measurable_fun_sum _ fun i _=>?_)
   let tr V:= call ((planted (vary X V) u.toLeft).taggedL i) (Z.capacityP u (own u.toLeft))
   let W d:= preps (X.taggedL i) {(roster u.toLeft) with flags:=d}; let g (d:Support c) (V) := if RG.flags (Pressure.temp X.x) V=d then call (vary (W d) V) (Z.capacityP u (own u.toLeft)) else 0
   have he' V: (∑ d,g d V)=tr V:=by unfold g tr W; rw [sum_ite_eq]; simp only [mem_univ,if_true]; rfl
   change Measurable tr; rw [← funext he']; refine Finset.measurable_fun_sum _ fun j _=>?_
   let A:= (Grid c × F.Slice su) × Air f su; let D:=(F.order su); let X':= W j
   let P': Grid c→F.Slice su → Air f su→EvenA c N:=fun V y z=> Z.capacityP u (own u.toLeft) (Art.drive X' V y) z
   let F₀ (x:A):=lens₀ ((vary X' x.1.1).relating) x.2 • P' x.1.1 x.1.2 x.2
   let Q:(V:Grid c)→EvenA c N:=fun V=> ∫ y,(∫ z,F₀ ((V,y),z)) ∂ D
   have hL : Measurable Q:=by
     let v (i:A):= i.1.1; have hv:Measurable v:=measurable_fst.comp measurable_fst
     have hh := c_measured X'.shutter (A:=fun i=> (vary X' (v i)).plate) (fun i j=> (Art.borel_plate X' H.laws.intake.ready i j).comp hv)
     have he': Measurable F₀:= (Shield.bulbB hh.1 (measurable_snd : Measurable fun i:A=>i.2)).smul (glassB Y (X:=X') u h he hk hv (measurable_snd.comp measurable_fst) measurable_snd)
     exact ((he'.stronglyMeasurable.integral_prod_right' (ν:=volume)).integral_prod_right' (ν:=D)).measurable
   have hv: g j= fun V=> if RG.flags (Pressure.temp X.x) V=j then Q V else 0:=by
     funext V; unfold g; split
     next hV=>
       let N':=vary X' V; have hN:N'.manifest:=hV.symm
       have hi:= (H.laws.data.localP F N' he hk hN).sails.fullC
       change call N' (Z.capacityP _ _)=Q V
       unfold call; rw [integral_prod _ (envPlot (Z.ripeP _ u (Y.forwarded F hp) N' he hk hN) _)]
       apply integral_congr_ae; filter_upwards with y
       have hθ:N'.dice= volume.withDensity (fun x=> ENNReal.ofReal (Shield.lens₀ N'.relating x)):= magnifies N'.relating hi
       rw [hθ, integral_withDensity_eq_integral_toReal_smul (show Measurable (fun i=> ENNReal.ofReal (lens₀ N'.relating i)) from ENNReal.measurable_ofReal.comp (bulbB (S:=fun _:Air f su=> N'.relating) (fun i j=>measurable_const) (z:=id) measurable_id)) (ae_of_all _ fun _=> ENNReal.ofReal_lt_top)]
       apply integral_congr_ae; filter_upwards with x; rw [ENNReal.toReal_ofReal (Shield.fullFuel ..).le]; rfl
     next _=> rfl
   rw [hv]; exact Measurable.ite (flags_measurable_eq ..) hL measurable_const
end YM.QCD.Loom.Fleet
