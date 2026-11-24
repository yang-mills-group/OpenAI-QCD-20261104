import YM.Play.Hut
import YM.Play.Skies
import YM.Hypnos.Cirque
import YM.MassiveQCD.Cupola.Dollar
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
local notation "Cv"=> month (P₀:=P₀) M G p
local notation "sp" r=> prism T τ χ o.K U (allot r)
local notation "Sp" r=> planted (prism T τ χ o.K U (allot r)) (∅:Finset (Head S))
variable (hV:(united (closet H G M X z a) Y).Famous)
variable (Ω:Support c) (hM:M=roof G P₀ 30 (radiusB τ))
open Hypnos
variable (Z:Coat T F)(hZ:Z.manifest)(htZ:Z.x=τ)(hwZ:Z.width=o.K)
-- every interested trial (even D pin where separated) might need health on its FULL main support AND all its halos. 
def owned (p:Finset (Fj D E J))(Ω:Support c):Prop:= ∀ i ⊆p, Burke P₀ G i → i.biUnion M ⊆ Ω
variable (h₀:owned G M p Ω) (w':Air f su)(hc:Calm Z Ω o.ξ β w') (hn:∀ i∈Ω,¬ Inside i Z.seeds (30*Z.B))
include H he h₀ htZ hwZ hZ hV hc
lemma nocturne (i:Ip): (Tx).coming (.inl (child G M p i)) Z w'=Β (X.hue O.threshold G i.val (Z.input (Z.liftA β w'))):=by
    let j:= child G M p i; let t':= Z.input (Z.liftA β w'); let y:=X.hue O.threshold G i.val t'; let K:=(Tx).window (.inl j); let Qx:= Z.plaza K
    have hp:= (mem_powerset.mp (mem_filter.mp i.2).1); have hL : i.val.biUnion M⊆ Ω:=h₀ _ hp (mem_filter.mp i.2).2.2
    have hQ p (hp:p∈Qx): atEdge S p∈Ω:=by
        obtain ⟨k,hk,hk'⟩:=Finset.not_disjoint_iff.mp (mem_filter.mp hp).2.2; have h:= stride p hk' -- check
        have hz:100 ≤ radiusB τ:= H.laws.data.room.sight.1; exact hL (hV.boot (.inl j) (halo_spec.mpr ⟨k,hk,h.trans (by omega)⟩))
    have hβ:0<β:= H.laws.intake.positive
    change Z.enforce (2*o.a) (Z.liftA β w') Qx • (δ⁻¹ ^Loom.budget P₀ i.val • Β y)= _
    rw [(enact Z Ω (htZ.symm ▸ H.laws.data) hwZ hZ hc hβ _ hQ).2]; unfold Loom.budget; rw [spentP _ _ hp he]; simp only [Rise.wish,biUnion_empty,Finset.card_empty,pow_zero,one_smul]; rfl

omit he hV
include hn hM
lemma vivifies (hh:SliceRows.Stamp T)(i:Finset (Fj D E J))(hi:i⊆p)(hb:Burke P₀ G i): Healthy O.threshold (brimW G P₀ i) (Z.input (Z.liftA β w')):=by
   have hp : (petal G P₀ i).image S.ratio.parent⊆ Ω:=by
       refine Subset.trans ?_ (h₀ i hi hb); rw [hM]; exact Subset.trans (halo_subset ..) (planet G P₀ i)
   refine safe_H Z Ω (htZ.symm ▸ H.laws.data) hwZ hZ hh hc (show 0<β from H.laws.intake.positive) hn _ ?_ ?_
   · intro i hv; apply hp; refine mem_image_of_mem _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,?_⟩)); rw [if_neg (fun hh=>hv hh.symm)]; unfold touched; apply List.mem_toFinset.mpr; simp [Lattice.visits,square]
   have hp:= H.laws.intake.received.temp; change O.threshold=_ at hp; change fiery _ _ _ /4 ≤ _; rw [htZ,hp]; linarith [H.laws.data.room.fiery] -- edit

-- bank capture cylinder
omit h₀ -- may he omitted
open Stitch.Tablet Cupola
variable (K₀:Finset E)(O₀: Finset D)
local notation "Pq" => pin O₀ K₀ (∅:Finset J)
local notation "Hz"=> (withdraw N z' a)
variable [Countable E][Countable J]
include hV hc hw hk
omit [Countable E] [Countable J]
lemma thirst (hp:owned (P₀:=P₀) G M (pin O₀ K₀ (∅:Finset J)) Ω) (hh:SliceRows.Stamp T)(ha:0<a):
   let X' := Z.input (Z.liftA β w'); let T:=(wipeL G X').comp ((birth (∑ i∈O₀,G.treats i X')).comp (nearL f c N)); let C:= ∑ i∈K₀,X.read O.threshold X' i
   light _ (Hz (skyM H G M X z a Y Pq F Z w'))=carry (Spine I) T (light _ (NormedSpace.exp C)):=by
    intro X₀' L C'; let V:=skyM H G M X z a Y Pq F; have hv:= oak X G hw M hk X₀' O₀ K₀ (vivifies H G M Pq Ω hM Z hZ htZ hwZ hp w' hc hn hh)
    refine Eq.trans ?_ hv
    apply congr_arg; rw [symphony G M Pq]; unfold skyM; rw [map_sum,sum_image]; swap; · exact (Finset.image_injective Subtype.val_injective).injOn
    refine sum_congr rfl fun i _=> ?_; unfold weald; rw [map_prod,prod_image Subtype.val_injective.injOn]; apply prod_congr rfl; intro j hj; rw [nocturne H G M X z a Y Pq (pinK ..) hV Ω Z hZ htZ hwZ hp w' hc j]; exact Cupola.home N z' a ha _
end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.thirst
