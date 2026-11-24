import YM.MassiveQCD.Apron.Color
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
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (R':Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "Gm"=> deckHue H G P₀ R'
local notation "M"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
variable [Fintype D][Countable E][Countable J]
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ R')
local notation "Ξ"=> closet H G R' X z a
local notation "Β"=>banknote N z' a
variable {p₁:E→ℝ}{p₂:J→ℝ}{m:D→ℝ}{r s u η h γ:ℝ}
variable (hh:X.Coins p₁ p₂ h O.threshold)(hc:Peak G O.threshold h a r m)(hδ:0<δ)
local notation "b!"=> mintD H G P₀ R' m p₁ p₂ r

local notation "GP"=> trimP T O δ β b
lemma beret (V:Grid c)(U:Grid f)(dec:0<δ)(Jx:Cove.Count G P₀ R')(l:Finset (Wound R')):
    ((Ξ).suitcase F).stumpP V l U=if ((Ξ).suitcase F).eligibleP l then Real.exp ((GP).exponent U) • (Β (X.dyes t G U (l.image Subtype.val))) else 0 :=by
   unfold stumpP; split; swap; · rfl
   next he=>
   let V':=((Ξ).suitcase F); let s:= l.image Subtype.val
   have hv : V'.filterP l= typo (P₀.wish (spent (s.biUnion id))):=by rw [countP]; unfold filterP s typo; rw [biUnion_image, image_biUnion]; rfl
   rw [show ((Ξ).suitcase F).filterP l= _ from hv]; unfold trimP; dsimp only; rw [keynote]
   unfold Stitch.Tablet.dyes; change (Real.exp ((GP).exponent U)*(if _ then _ else _)) • _= Real.exp _ • (Β (if P₀.wish (spent (s.biUnion id)) =_ then _ else _))
   rw [mul_smul]; congr 1; split
   swap; · rw [map_zero,zero_smul] -- may also if
   next h=>
   let b:=fun i:Wound R'=>budget P₀ i.val
   have hv : (P₀.wish (spent (s.biUnion id))).card=∑ i∈l,b i:=by
      rw [countP,card_biUnion]; swap; · intro i hi j hj hz; exact fittingX G P₀ R' Jx (show Disjoint _ _ from (show _ ∧_ from ((exc (F:=F) H G P₀ R' l).mp he)).1 hi hj hz)
      unfold s; rw [sum_image Subtype.val_injective.injOn]; rfl
   rw [hv,prod_image Subtype.val_injective.injOn,map_prod]
   let g i:=Β (X.hue t G (i:Wound R').val U)
   change _ • (∏ i∈l,δ⁻¹^(b i) • g i)= _
   rw [show (∏ i∈l,δ⁻¹^(b i) • g i)= (δ⁻¹)^(∑ i∈l,b i) • ∏ i∈l,g i from ?_,smul_smul,inv_pow, mul_inv_cancel₀ (pow_ne_zero _ dec.ne'),one_smul]
   rw [← prod_pow_eq_pow_sum (s:=l) (f:=b)]; simp_rw [← prod_coe_sort l]; exact prodSaddle .. -- inspect

lemma soul (V:Grid c)(U:Grid f)(dec:0<δ)(Jx:Cove.Count G P₀ R')(hx:X.Wave O.threshold q' z)(ht:X.Staid t U): HasSum (fun i=> ((Ξ).suitcase F).stumpP V i U) (Real.exp ((GP).exponent U) • Β (∑' i,X.caller t G R' U i)):=by
   let f l:= (l:Finset (Wound R')).image Subtype.val
   let e:=Real.exp ((GP).exponent U); let g i:= Β (X.caller t G R' U i)
   have he: Injective f:= Finset.image_injective Subtype.val_injective
   have ht: HasSum (fun i=> e • g i) (e • Β (∑' i,X.caller t G R' U i)):= ((Stitch.Tablet.cashS X t G Jx U hx ht).hasSum.map (Β) ((Β).toLinearMap.continuous_of_finiteDimensional)).const_smul _
   refine ((he.hasSum_iff (fun i hi=> ?_)).2 ht).congr_fun ?_
   · unfold g Stitch.Tablet.caller; split; swap; · rw [map_zero,smul_zero]
     next hh=>
       let d (j:↥i): Wound R':= ⟨j.val, hh.2 _ j.property⟩
       apply False.elim; apply hi; refine ⟨i.attach.image d, ?_⟩; ext x; simp only [f,mem_image, mem_attach,true_and]; refine ⟨?_,fun h=> ⟨_,⟨⟨x,h⟩,rfl⟩,rfl⟩⟩; rintro ⟨z,⟨b,rfl⟩,rfl⟩; exact b.property
   intro i; rw [beret H G R' X z a V U dec Jx, show ((Ξ).suitcase F).eligibleP i ↔ i.image Subtype.val∈taxes R' from (exc (F:=F) H G P₀ R' i)]; unfold Function.comp g Stitch.Tablet.caller; split
   next h=> dsimp only; rw [if_pos (show f i ∈taxes R' from h)]; rfl
   next h=> dsimp only; rw [if_neg (show f i ∉taxes R' from h),map_zero,smul_zero]

end YM.MassiveQCD.Apron
