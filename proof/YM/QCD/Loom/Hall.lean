import YM.QCD.Loom.Harmony
/-! # hue stamps AND restoration of K column tokens -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R : BudgetPoint}
variable {H:Cash W τ μ L Q o C T (trimP T R δ β b)}{ι D E K:Type}{N:ℕ}
local notation "Ξ" => Fj D E K
variable (H :Cash W τ μ L Q o C T (trimP T R δ β b)) (Y:Send S.ratio N D)(p:Rise f N E K)(X:Fj D E K→Support c)
variable [Fintype D][Countable E][Countable K]
local notation "A" => Wound X
local notation "t"=>R.threshold
local notation "PI"=> trimP T R δ β b
local notation "Y'"=> (deckHue H Y p X)
lemma exc (l:Finset (Wound X)): ((Y').suitcase F).eligibleP l ↔ l.image Subtype.val ∈ taxes X:=by
   unfold taxes; simp only [Set.mem_setOf_eq]; let v:=fun s:↥l=>s.val.val
   constructor
   · intro hb; constructor
     · rintro i hi j hj h; obtain ⟨a,ha,rfl⟩:=mem_image.mp hi; obtain ⟨b,hb',rfl⟩:=mem_image.mp hj; exact hb ha hb' (fun he=>h (he ▸ rfl))
     intro i hi; obtain ⟨a,ha,rfl⟩:=mem_image.mp hi; exact a.2
   intro he i hi j hj hl; exact he.1 (mem_image_of_mem Subtype.val hi) (mem_image_of_mem Subtype.val hj) (fun h=>hl (Subtype.ext h))
lemma fittingX {s u:Finset Ξ}(h:Cove.Count Y p X)(he: Disjoint (s.biUnion X) (u.biUnion X)):
    Disjoint (p.wish (spent s)) (p.wish (spent u)):=by
   refine Finset.disjoint_left.mpr (fun i hi hj=>?_)
   have hv s (he:i∈p.wish (spent s)): S.ratio.parent i ∈s.biUnion X:=by
      obtain ⟨b,hb,hy⟩:=mem_biUnion.mp (show i∈brimW Y p s from (native_sub Y p s) (wish_sub Y p s he))
      exact mem_biUnion.mpr ⟨b,hb,h.1 b (mem_image_of_mem _ hy)⟩ -- inspect
   exact Finset.disjoint_left.mp he (hv s hi) (hv u hj)
lemma countP (s: Finset (Finset Ξ)): p.wish (spent (s.biUnion id))= s.biUnion (fun i=>p.wish (spent i)):=by ext j; simp only [Rise.wish,mem_biUnion,spent,mem_toRight,id_eq]; grind
lemma beret (V:Grid c)(U:Grid f)(dec:0<δ)(Jx:Cove.Count Y p X)(l:Finset (Wound X)):
    ((Y').suitcase F).stumpP V l U=if ((Y').suitcase F).eligibleP l then Real.exp ((PI).exponent U) • Cove.dyes Y p t U (l.image Subtype.val) else 0 :=by
   unfold stumpP; split; swap; · rfl
   next he=>
   let V':=((Y').suitcase F); let s:= l.image Subtype.val
   have hv : V'.filterP l= typo (p.wish (spent (s.biUnion id))):=by rw [countP]; unfold filterP s typo; rw [biUnion_image, image_biUnion]; rfl
   rw [show ((Y').suitcase F).filterP l= _ from hv]; unfold trimP; dsimp only; rw [keynote]
   unfold Cove.dyes; change (Real.exp ((PI).exponent U)*(if _ then _ else _)) • _= Real.exp _ • (if p.wish (spent (s.biUnion id)) =_ then _ else _)
   rw [mul_smul]; congr 1; split
   swap; · rw [zero_smul] -- may also if
   next h=>
   let b:=fun i:Wound X=>budget p i.val
   have hv : (p.wish (spent (s.biUnion id))).card=∑ i∈l,b i:=by
      rw [countP,card_biUnion]; swap; · intro i hi j hj hz; exact fittingX Y p X Jx (show Disjoint _ _ from (show _ ∧_ from ((exc (F:=F) H Y p X l).mp he)).1 hi hj hz)
      unfold s; rw [sum_image Subtype.val_injective.injOn]; rfl
   rw [hv,prod_image Subtype.val_injective.injOn]
   let g i:=hue Y p t (i:A).val U
   change _ • (∏ i∈l,δ⁻¹^(b i) • g i)= _
   rw [show (∏ i∈l,δ⁻¹^(b i) • g i)= (δ⁻¹)^(∑ i∈l,b i) • ∏ i∈l,g i from ?_,smul_smul,inv_pow, mul_inv_cancel₀ (pow_ne_zero _ dec.ne'),one_smul]
   rw [← prod_pow_eq_pow_sum (s:=l) (f:=b)]; simp_rw [← prod_coe_sort l]; exact prodSaddle .. -- inspect
lemma soul (V:Grid c)(U:Grid f)(dec:0<δ)(Jx:Cove.Count Y p X)(hx:p.Wave t)(ht:Placid p t U): HasSum (fun i=> ((Y').suitcase F).stumpP V i U) (Real.exp ((PI).exponent U) • ∑' i,Cove.caller Y p t X U i):=by
   let f l:= (l:Finset (Wound X)).image Subtype.val
   let e:=Real.exp ((PI).exponent U); let g i:= Cove.caller Y p t X U i
   have he: Injective f:= Finset.image_injective Subtype.val_injective
   have ht: HasSum (fun i=> e • g i) (e • ∑' i,g i):= ((cashS Y p t Jx U hx ht).hasSum).const_smul _
   refine ((he.hasSum_iff (fun i hi=> ?_)).2 ht).congr_fun ?_
   · unfold g caller; split; swap; · rw [smul_zero]
     next hh=>
       let d (j:↥i): Wound X:= ⟨j.val, hh.2 _ j.property⟩
       apply False.elim; apply hi; refine ⟨i.attach.image d, ?_⟩; ext x; simp only [f,mem_image, mem_attach,true_and]; refine ⟨?_,fun h=> ⟨_,⟨⟨x,h⟩,rfl⟩,rfl⟩⟩; rintro ⟨z,⟨b,rfl⟩,rfl⟩; exact b.property
   intro i; rw [beret H Y p X V U dec Jx, (exc H Y p X i)]; unfold Function.comp g caller; split
   next h=> dsimp only; rw [if_pos (show f i ∈taxes X from h)]
   next h=> dsimp only; rw [if_neg (show f i ∉taxes X from h),smul_zero]
end YM.QCD.Loom
