import YM.QCD.Loom.Lush
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Greenbelt

/-!
# Independent forest marquee. V leaf & wider law.
-/
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
def fullA (Y:Fleet H ι N) (s:I): Support c:= s.biUnion (Sum.elim H.supportP Y.ground)
lemma aliveP (i:ι)(h:Y.Famous){X:C' F}{X':C' Z}{W: Support c} (hv:Y.ground i ⊆ W){a b:Finset ℕ}{w v: Air f su}(he:X.x=τ)(ht: ConnectedActivityE6.Clump X X' W w v a b R) : Y.coming i X w=Y.coming i X' v:=by
   have hB : Room P S T X.x := he.symm ▸ H.laws.data.room
   have he' x (hi:x∈Y.window i): Cleanroom W (30*X.B) x:=fun y hy=>hv (h.boot i (halo_spec.mpr ⟨_,hi,(show separation x y ≤30*radiusB τ from congrArg (fun b=>30*radiusB b) he ▸ hy)⟩))
   unfold coming riseP; rw [ht.enforces hB _ he']; congr 1
   rw [h.read i (X.input (X.liftA R.beta w)) X.V X'.V (agrees_mono ht.actual fun _ hi=>hv (((halo_subset ..).trans (h.boot i)) hi))]
   exact h.locally i _ _ _ (fun p h₁ _=> ht.quarters hB (fun j hx=> he' _ (h.horizons i (mem_image_of_mem _ h₁)) j (hx.trans (mul_le_mul_of_nonneg_right (by omega) (Nat.zero_le _)))))
lemma roofP (s:I)(h:Y.Famous){X:C' F}{X':C' Z}{w v: Air f su}{a:Finset ℕ}(he:X.x=τ)(ht : ConnectedActivityE6.Clump X X' (Y.fullA s) w v a a R): (Y.suitcase F).capacityP s a X w=(Y.suitcase Z).capacityP s a X' v:=by
   unfold Pipe.capacityP; congr 1
   · refine prod_congr rfl fun i hi=> ht.complete (he.symm ▸ H.laws.data.room) Q.buys i ?_ (he.symm ▸ H.laws.intake) o.a W Q.table
     change Mixed.foot S _ (radiusB X.x) (footprints _ R _ (radiusB X.x)) i⊆_
     rw [he]; exact ((subset_biUnion_of_mem H.supportP hi).trans ((Y.suitcase F).lesserP s))
   exact prod_congr rfl fun i hi=> aliveP Y i h ((Y.suitcase F).leP s hi) he ht
lemma casesP (s:I)(h:Y.Famous){a:Finset ℕ}(X:C' F)(X':C' Z)(he:X.x=τ)(hz:X'.x=τ)(hX:X.width=o.K)(hX':X'.width=o.K)(hx:X.manifest)(hx':X'.manifest)(hp:∀ u:Grid f,Crop (X.wrapY (bridge (S:=S) F u)) (X'.wrapY (bridge (S:=S) Z u)) (Y.fullA s)) : call X ((Y.suitcase F).capacityP s a)=call X' ((Y.suitcase Z).capacityP s a):=by
   let Yf (i: F.Slice su×Air f su):= (Y.suitcase F).capacityP s a (X.wrapY i.1) i.2
   let Yz (i: Z.Slice su×Air f su):= (Y.suitcase Z).capacityP s a (X'.wrapY i.1) i.2
   let p:= podium S su (Y.fullA s) X.B
   have ht:= (Y.suitcase F).ripeP a s (Y.forwarded F h) X he hX hx
   have hv:= (Y.suitcase Z).ripeP a s (Y.forwarded Z h) X' hz hX' hx'
   apply concrete; intro l
   have hm:=envPlot ht ((F.order su).prod X.dice); have hn:=envPlot hv ((Z.order su).prod X'.dice)
   change l (∫ i,Yf i ∂_)=l (∫ i,Yz i ∂_)
   rw [← ContinuousLinearMap.integral_comp_comm _ hm,← ContinuousLinearMap.integral_comp_comm _ hn, integral_prod _ (l.integrable_comp hm),integral_prod _ (l.integrable_comp hn)]; erw [← Pond.reception (reserve (S:=S) su F) _ ((l.measurable.comp ht.meas).stronglyMeasurable.integral_prod_right' (ν:=X.dice)).measurable, ← Pond.reception (reserve (S:=S) su Z) _ ((l.measurable.comp hv.meas).stronglyMeasurable.integral_prod_right' (ν:=X'.dice)).measurable]
   apply integral_congr_ae; filter_upwards with u
   have hC : circuit p X.relating=circuit p X'.relating:=by ext i j; have hh: Room P S T (X.wrapY (bridge (S:=S) F u)).x:=he.symm ▸ H.laws.data.room; exact (hp u).same_cov hh j.val j.2 i.val
   have hT : MeasurePreserving (Pond.swim p) X.dice (arch p X.relating):= Pond.orbit (H.laws.data.localP F X he hX hx).sails.fullC.posSemidef p
   have hZ : MeasurePreserving (Pond.swim p) X'.dice (arch p X.relating):= by unfold arch; rw [hC]; exact Pond.orbit (H.laws.data.localP Z X' hz hX' hx').sails.fullC.posSemidef p
   let f₀ i:= l (Yf (bridge (S:=S) F u,i)); let g i:=l (Yz (bridge (S:=S) Z u,i))
   have hi i j (hw : Pond.swim p i=Pond.swim p j):f₀ i=g j:=congr_arg l (roofP Y s h (X:=X.wrapY (bridge (S:=S) F u)) (X':=X'.wrapY (bridge (S:=S) Z u)) he ⟨hp u,(observe _).1 hw,fun _ _=> Iff.rfl⟩)
   change (∫ i,f₀ i ∂X.dice)=∫ i,g i ∂X'.dice
   rw [gathered (f:=f₀) (spill p) (spill_m p) hT (Pond.settled p) (fun i j h=>(hi i j h).trans (hi j j rfl).symm) (l.measurable.comp (ht.meas.comp (measurable_const.prodMk measurable_id))), gathered (f:=g) (spill p) (spill_m p) hZ (Pond.settled p) (fun i j h=>(hi i i rfl).symm.trans (hi i j h)) (l.measurable.comp (hv.meas.comp (measurable_const.prodMk measurable_id)))]
   exact integral_congr_ae (ae_of_all _ fun i=> hi _ _ rfl)
lemma spacial (s:I)(h:Y.Famous)(X:C' F)(X':C' Z)(he:X.x=τ)(hz:X'.x=τ)(hX:X.width=o.K)(hX':X'.width=o.K)(hx:X.χ=X'.χ)(hp:Agrees (Y.fullA s) X.V X'.V)(hw : (Y.fullA s)∩RG.flags (Pressure.temp τ) X.V= (Y.fullA s)∩RG.flags (Pressure.temp τ) X'.V)(hc : ∀ i : Site f,S.ratio.parent i∈Y.fullA s→F.up i=Z.up i) : (Y.suitcase F).shootsP X s=(Y.suitcase Z).shootsP X' s:=by
   unfold Pipe.shootsP; refine if_congr ?_ ?_ rfl
   · rw [he,hz, inter_comm (s₁:=RG.flags (Pressure.temp τ) X.V),inter_comm (s₁:=RG.flags (Pressure.temp τ) X'.V), show (Y.suitcase F).full s ∩ RG.flags _ _ = _ from hw]; rfl
   let f:= Matter.planted X s.toLeft; let g:= Matter.planted X' s.toLeft
   unfold draws; apply congr_arg choiceS; funext k
   apply casesP Y s h (f.taggedL k) (g.taggedL k) he hz hX hX' (Matter.planted_valid X _) (Matter.planted_valid X' _)
   intro u; refine ⟨he.trans hz.symm,hX.trans hX'.symm,hx,fun i hi=>?_, foreclose hc u,fun _ _=>rfl,fun _ _=>rfl,hp⟩
   have hT : i∈RG.flags (Pressure.temp X.x) X.V↔ i∈ RG.flags (Pressure.temp X'.x) X'.V:=by simpa only [he,hz,mem_inter,hi,true_and] using Finset.ext_iff.mp hw i -- using goal elaboration
   change i∈ f.seeds.place ↔ i∈g.seeds.place
   unfold f g Matter.planted Stores.place; dsimp only [preps]; simp_rw [mem_union]; exact or_congr Iff.rfl hT
end YM.QCD.Loom.Fleet
