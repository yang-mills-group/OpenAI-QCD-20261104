import YM.Cardinal.Ficus
import YM.Oars.Lavender
import YM.Cardinal.Dot
import YM.Cardinal.Obel
import YM.Cardinal.Alton
import YM.Massive.Horizon.Solo
import YM.Massive.Horizon.Castle
import YM.Poised.Votes
/-! # Bridge Cupola and Siege.Tower: paid on ONE trajectory -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Lyre
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable {P₁:Plan j}{a₀ b₀ a₁ b₁ w mm :ℝ}{E₁:Offer 1 a₀ a₁}{E₂:Offer 2 b₀ b₁}
local notation "Xγ"=> (pesto P₁ L' d (trunkM E₁ E₂ w mm f))
variable (G:Sun L' c f d η h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ w mm f))) (U :Swathe L' d (pesto P₁ L' d (trunkM E₁ E₂ w mm f)) W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
namespace Drawing.Claro
open Massive.Poised QCD.Shells Cupola Plate Card Iris Puff Patron
open Ac QCD.Cove.Send Warmlet Push.Local Massive.Poised.Plans Massive.Poised.Plans.Stamp
open Massive.UV
variable {E' K':Type}{q': Bool}
structure Charter {I Gp:Type}[Fintype I](P': Rise f N E J)(Q: Puff f N E' q')(T:Film f N I K') where
  P : Reel f N I Gp
  rd : Twist.Register P' P T
  demand : Set (Finset I)
  K0 : I
  hold : {K0}∈ demand
  o : I → Cover -- include K1 A alignment below.A should used globally for K0. use A via update
  style : I→Bool
  port : style K0=q'
  parts: E' ↪ Gp
  bears(i:E'): P.z (parts i)= {K0}
  emb (i:E') : P.addr (parts i)=Q.addr i
  source(i:E'): Reel.speaker style P (parts i)=Q.fill i
  exactParts (g:Gp): P.z g={K0} → g ∈ Set.range parts
namespace Charter
variable {I Gp:Type}[Fintype I]{Qv:Puff f N E' q'}{Tv:Film f N I K'} (X: Charter (Gp:=Gp) P₀ Qv Tv)
noncomputable abbrev ear:= X.parts.trans X.rd.ear
lemma homeP (i:E') : P₀.row (X.ear i)= Qv.addr i:= (X.rd.homeP (X.parts i)).trans (X.emb i)
noncomputable abbrev loc (A:Cover): I→Site f:= fun i=> if i=X.K0 then wrap f A else wrap f (X.o i)
lemma stepEq(A:Cover): X.loc A X.K0=wrap f A:=if_pos rfl
noncomputable abbrev V := Twist.result P₀ X.P Tv X.rd
lemma offer (i:E') : X.V.spine (X.ear i)={X.K0}:= (Twist.figures P₀ X.P Tv X.rd (X.parts i)).2.trans (X.bears i)
-- restricted index subtype by just exact singleton; demand trivial by hold
noncomputable abbrev Role {c:Side}(p:I→Site c)(Γ: Gem c (ample N I) D)(ψ:D→Finset I):= {i:D// ψ i={X.K0} ∧ (ψ i).image p⊆ (Γ.addr i).support}
noncomputable def helm {c:Side}(p:I→Site c)(Γ:Gem c (ample N I) D)(ψ:D→Finset I)(i:X.Role p Γ ψ): Reel.Answer N p Γ ψ X.demand:=⟨i.val, i.property.1.symm ▸ X.hold,i.property.1.symm ▸ singleton_nonempty _,i.property.2⟩
end Charter
-- Pu.N
variable {IE Gp:Type} [Fintype IE]
variable (Qx:Puff f N E' q')(Tq:Film f N IE K')(Oq: Charter (Gp:=Gp) P₀ Qx Tq)
variable (A A' :Cover) (Qe: Seal N (wrap f A) Qx)
local notation "Aᴮ"=>Oq.loc A
set_option quotPrecheck false
local notation "A⁺"=> ((S').ratio.parent ∘ (Aᴮ))
local notation "Tᴮ"=>fun (_:Unit)=>wrap c A'
local notation "K₀"=> ({Oq.K0}:Finset IE)
local notation "qᴮ"=>Oq.style
local notation "Y"=> Oq.V
variable (φ:ℝ)
local notation "B"=>radiusB τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=>QCD.Jets.Touch.roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "S₁"=>united (VarnC H U N) (sailP H Γ N)
local notation "Tx"=> vantage L' d K H G U Γ (Y) (Aᴮ) φ
local notation "U₀"=>Warmlet H S₁ (Z') P₀
local notation "D'"=>Sum.elim (fun u:Wound Zⁱ=> (Y).markers u.val) (fun _: Varn f c⊕Gaze c=>∅)
local notation "χ'"=>swingE N Tx D'
set_option quotPrecheck false
open Warmlet MassiveQCD.Lyre Sands
variable {χ:Chi}{α ξ θ t t₀ x x₀ x₁ κ α₁ α₂ ε:ℝ}{P₂: BudgetPoint}
variable (X:Clusters (vantage L' d K H G U Γ (Oq.V) (Oq.loc A) φ).Bright → RegularAddress c)
variable (hM:∀ i,(X i).support= GasP.seatP ((vantage L' d K H G U Γ (Oq.V) (Oq.loc A) φ).lightF) i)
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "Cⁱ"=> crude Tx χ X
local notation "a⁺"=>  budAtlas (A⁺) (30*B)
local notation "I✡"=> Oq.Role (A⁺) (Cⁱ) (χ')
local notation "E✡"=> (Reel.render N (A⁺) φ t₀ Cⁱ (χ') Oq.demand)
local notation "H✡"=> Oq.helm (A⁺) Cⁱ (χ')
local notation "Z✡"=> Reel.speaker (qᴮ) (E✡) ∘ H✡
variable (hSup:Supplies L' d K H G U Γ (Oq.V) (Oq.loc A) φ χ (Oq.style) t θ P₂.order P₂.power)
local notation "kindY"=> (address H S₁ (Z') P₀)
local notation "ι'"=> Clusters (Tx).Bright
-- naming geometry
noncomputable def aisle (j: Clusters (vantage L' d K H G U Γ (Oq.V) (Oq.loc A) φ).Bright): Support c:=if h:∃ (i: Warmlet H (united (VarnC H U N) (sailP H Γ N)) (G.equip N (radiusB τ)) P₀),individual i.code=j then (trunkP H S₁ (Z') P₀ F' (Classical.choose h)).support else (X j).support -- arg individual type named
local notation "Iⁱ"=> aisle L' d K H G U Γ Qx Tq Oq A φ X F'
include hM
lemma plumed (i: U₀) : (X (individual i.code)).support=past H S₁ (Z') P₀ i:= (hM _).trans (Sands.cottage Tx i.code (.inl i.label) i.earns).1
omit hM
lemma stride (i: U₀): (Iⁱ) (individual i.code)= (trunkP H S₁ (Z') P₀ F' i).support:=by
    unfold aisle; split; next h=> rw [show Classical.choose _=i from copyQ H S₁ (Z') P₀ _ _ (Classical.choose_spec h)]
    next h=> exact False.elim (h ⟨i,rfl⟩)
include hM
lemma grows (i:ι') : (X i).support⊆ Iⁱ i∧ Iⁱ i⊆ Lattice.halo (Q.halo* B) (X i).support:=by
    unfold aisle; split; next h=> let j:=Classical.choose h; have hj: individual j.code=i:= Classical.choose_spec h; rw [show (X i).support=past H S₁ (Z') P₀ j from hj ▸ plumed L' d K H G U Γ Qx Tq Oq A φ X hM j]; exact (Warmlet.groom ..).2
    next _=> exact ⟨Subset.refl _,halo_subset ..⟩
include hSup
lemma spindle (j:I✡): (a⁺ Oq.K0) ⊆ (X j.val).support:=by
    have hj:= wingSpan L' d K H G U Γ Y (Aᴮ) φ qᴮ hSup j.val
    have hx:χ' j.val={Oq.K0}:=j.property.1; rw [hM j.val]; exact (mem_filter.mp (hj (hx.symm ▸ mem_singleton_self _))).2
-- naming to registers. call handles.N.Type.
omit hM hSup
lemma enlist (i:E) : ( (kindY).symm i).val.label.val={Sum.inr (.inl i)}:= by
    let j:= (kindY).symm i; have he:=duke H S₁ (Z') P₀ j; rw [show col _ _ _ _ j=i from (kindY).apply_symm_apply _] at he; exact he
lemma stamps (i:E') : swingE N Tx D' (individual ((kindY).symm (Oq.ear i)).val.code)= K₀:=by
    let j:= ((kindY).symm (Oq.ear i)).val; have hx:= ((slate H S₁ (Z') P₀ j (Oq.ear i)).1 (enlist L' d K H G U Γ (Oq.ear i))).1; exact (name_stamp L' d K H G U Γ Y Aᴮ φ j).trans ((markUp (Y) j.label.val (stop H S₁ (Z') P₀ j) hx).trans (Oq.offer i))
 where
    markUp {E J R I:Type}[Fintype I]{V:Rise f N E J}(X: Stitch.Tablet V I)(U: Finset (Fj R E J))(hx:spent U=∅){t:E}(hp:leftE U={t}) : X.markers U=X.spine t:=by rw [Stitch.Tablet.markers,hx,hp,singleton_biUnion,biUnion_empty,union_empty]
include hM
include Qe
lemma enters (i:E'): ∃ A:I✡, A.val= individual ((kindY).symm (Oq.ear i)).val.code:=by
    let j:= ((kindY).symm (Oq.ear i)).val; let J:ι':=individual ((kindY).symm (Oq.ear i)).val.code; have hK: χ' J= {Oq.K0}:=stamps L' d K H G U Γ Qx Tq Oq A φ i; refine ⟨⟨J,hK,?_⟩,rfl⟩; rw [hK]; change image _ _⊆ (X J).support; rw [image_singleton,show (X J).support=past H S₁ (Z') P₀ j from plumed L' d K H G U Γ Qx Tq Oq A φ X hM j]
    refine Finset.singleton_subset_iff.mpr ?_; rw [old_eq,show j.label.val=_ from enlist L' d K H G U Γ (Oq.ear i), singleton_biUnion]; -- need hQ anchor and given.Covers
    change A⁺ Oq.K0 ∈ Lattice.halo _ (Finset.image _ _); apply halo_subset; change (S').ratio.parent (Oq.loc A Oq.K0)∈_; rw [Oq.stepEq]; apply mem_image_of_mem; apply Finset.mem_union_left; apply halo_subset; change wrap f A∈(P₀.row (Oq.ear i)).support; rw [Oq.homeP]; exact (Qe.anchor i) ▸ (Qx.addr i).anchor
noncomputable def towerE (he:Seal N (wrap f A) Qx) (hM:∀ i,(X i).support= GasP.seatP ((Tx).lightF) i) (i:E'): I✡:= Classical.choose (enters L' d K H G U Γ Qx Tq Oq A he φ X hM i)
-- Qe binder included? proof body doesn't include Qe need include for lemma definition.
lemma tower_step (i:E') : (towerE L' d K H G U Γ Qx Tq Oq A φ X Qe hM (χ:=χ) i).val= individual ((kindY).symm (Oq.ear i)).val.code:= Classical.choose_spec (enters L' d K H G U Γ Qx Tq Oq A Qe φ X hM i)
local notation "tower'"=> towerE L' d K H G U Γ Qx Tq Oq A φ X Qe hM (χ:=χ)
lemma tower_inj : Function.Injective (towerE L' d K H G U Γ Qx Tq Oq A φ X Qe hM (χ:=χ)):=by
   intro i j h; have hf:=congr_arg Subtype.val h; rw [tower_step,tower_step] at hf; apply Oq.ear.injective; apply (kindY).symm.injective; apply Subtype.ext; exact copyQ H S₁ (Z') P₀ _ _ hf
-- converse
lemma spar (j: U₀)(hp:(Y).markers j.label.val={Oq.K0})(q:E)(ht:Fj.leftE j.label.val={q}):∃ i:E',q=Oq.ear i :=by
   have he:= (markUp (Y) j.label.val (stop H S₁ (Z') P₀ j) ht).symm.trans hp
   by_cases hv: q∈ Set.range Oq.rd.ear
   · obtain ⟨i,h⟩:=hv; have hx: Oq.P.z i={Oq.K0}:=(Twist.figures P₀ Oq.P _ Oq.rd i).2.symm.trans ((congr_arg (Y).spine h).trans he)
     obtain ⟨b,hb⟩:=Oq.exactParts i hx; exact ⟨b,h.symm.trans (congr_arg _ hb.symm)⟩
   rw [show (Y).spine q= ∅ from (Twist.orient P₀ Oq.P _ Oq.rd q hv).2] at he; simp at he
 where
    markUp {E J R I:Type}[Fintype I]{V:Rise f N E J}(X: Stitch.Tablet V I)(U: Finset (Fj R E J))(hx:spent U=∅){t:E}(hp:leftE U={t}) : X.markers U=X.spine t:=by rw [Stitch.Tablet.markers,hx,hp,singleton_biUnion,biUnion_empty,union_empty]
set_option maxHeartbeats 750000 in
lemma tower_out (j:I✡)(K₁:U₀)(he: j.val= individual K₁.code)(ht: Warmlet.prince H S₁ (Z') P₀ K₁): j∈Set.range tower':=by
    let q:= kindY ⟨K₁,ht⟩; have hz: K₁.label.val={Sum.inr (.inl q)}:= duke H S₁ (Z') P₀ ⟨K₁,ht⟩
    have hw: (Y).markers K₁.label.val= swingE N Tx D' j.val:=(name_stamp L' d K H G U Γ Y Aᴮ φ K₁).symm.trans (congr_arg (swingE N Tx D') he.symm); have hx:(Y).markers K₁.label.val={Oq.K0}:= hw.trans j.property.1
    obtain ⟨i,hi⟩:= spar L' d K H G U Γ Qx Tq Oq A Qe φ X hM K₁ hx q (((slate H S₁ (Z') P₀ K₁ q).1 hz).1) -- inspect args
    let x:= ((kindY).symm (Oq.ear i)).val; have hy: x=K₁:= by unfold x; apply congr_arg Subtype.val (show (kindY).symm (Oq.ear i)= _ from (congr_arg ((kindY).symm) hi.symm).trans ((kindY).symm_apply_apply _)); 
    let L (p:U₀): ι' := individual p.code; have hp: (tower' i).val=L x:= tower_step L' d K H G U Γ Qx Tq Oq A Qe φ X hM (χ:=χ) i; exact ⟨i,Subtype.ext (hp.trans ((congr_arg L hy).trans he.symm))⟩
end Drawing.Claro
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.Drawing.Claro.tower_out
