import YM.QCD.Golden.Shades
/-! # joint geometry score, Used in same Fiscal. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false

open Pipe
-- score lengths, b extra constant unchanged? in units P b.extraSeed from H=0.
def worthX (u:I') :ℝ:=H.shapeW u.toLeft+∑ i∈u.toRight,(coverNumber (radiusB s) (Y.ground i):ℝ)
lemma worthG (u:I'): H.shapeW u.toLeft≤ worthX Y u∧0≤ worthX Y u:=by
    have he:H.shapeW u.toLeft≤worthX Y u:=le_add_of_nonneg_right (sum_nonneg fun i _=>Nat.cast_nonneg _)
    exact ⟨he,(H.positive_volume _).trans he⟩
def checkL (w:ι→ℝ)(a t:ℝ): Piece S ι→ℝ:= let P:=unitsP Q L μ R.beta s C' a t
 (Mixed.costs S Q.halo (radiusB s) (steamP S P) (Sum.elim Ξ.flair w))∘ shifts S ι
lemma scoreY (a t:ℝ)(u:I'): setPrice (Y.suitcase F).gP (radiusB s) ((Y.suitcase F).inks (unitsP Q L μ R.beta s C' a t) (fun _=>0)) u = worthX Y u:=by
    classical
    unfold setPrice worthX
    let f:= Reserves.weight (Y.suitcase F).gP (radiusB s) ((Y.suitcase F).inks (unitsP Q L μ R.beta s C' a t) (fun _=>0)); let l:=u.toLeft; let p:=u.toRight
    have he:l.disjSum p=u:=by ext i; rcases i with a|b <;> simp [l,p]
    change (∑ i∈u,f i)=H.shapeW l + ∑ i∈p,_
    rw [← he,sum_disjSum]; apply congr_arg₂ (·+·)
    · unfold Cash.shapeW; apply Finset.sum_congr rfl; rintro (i|i) _ <;> rfl
    apply sum_congr rfl; intro i hi; change _ + (0:ℝ)= (coverNumber _ _:ℝ); rw [add_zero]; rfl
lemma checkX (w:ι→ℝ)(a t:ℝ)(u:I') : (∏ i ∈ u,checkL Ξ w a t i) = Real.exp (a*(Y.suitcase F).sizeP u)*((∏ i∈u.toLeft,Ξ.fare i)*(∏ i∈u.toRight,w i)):=by
  let P:=unitsP Q L μ R.beta s C' a t; have he i: checkL Ξ w a t (Sum.inl i) = Real.exp (a*Mixed.shares S i)* Ξ.fare i:=by
    cases i with
    | inl x=>
       unfold checkL; simp only [Function.comp_apply,shifts,Equiv.sumAssoc_apply_inl_inl, Mixed.shares,Mixed.costs,Utopia.fare, stout, Sum.elim_inl]; split
       next h=> unfold steamP Packets.income; simp only [P,unitsP,Target.costs,Buy.quote,one_mul]; rw [← Real.exp_add]; apply congr_arg; ring
       next _=> rw [mul_zero]
    | inr z=> change Ξ.flair z= Real.exp (a*(0:ℕ))* Ξ.flair z; simp
  rw [cumulate,← (Y.suitcase F).whorls]; unfold tenn; change (∏ i∈u.toLeft,checkL Ξ w a t (.inl i))*(∏ i∈u.toRight,w i)=_
  simp_rw [he, Finset.prod_mul_distrib,← Real.exp_sum,← Finset.mul_sum,← Nat.cast_sum, mul_assoc]
lemma lensRent (H':Support c)(K:ℕ) : (edgesM S H' K).card≤ H'.card*Itinerary.density S.patch.L:=by
    let Y:= univ.filter fun i:Bond f=> atEdge S i∈H'; apply le_trans _ (perch S H'); apply card_le_card; intro i hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2 (atEdge S i) (by simp)⟩
lemma cupLength (u:I'): ((edgesM S (Y.fullA u) (radiusB s)).card:ℝ) ≤ worthX Y u * ballCost (radiusB s)* (Itinerary.density S.patch.L:ℝ) :=by
   let S':= Y.fullA u; let B:=radiusB s
   have hp:S'= H.unionP u.toLeft∪(u.toRight.biUnion Y.ground):=by
      ext i; change i∈u.biUnion _↔_; rw [mem_biUnion,mem_union, show H.unionP u.toLeft=u.toLeft.biUnion H.supportP from rfl,mem_biUnion,mem_biUnion]; constructor
      · rintro ⟨z,hp,hf⟩; rcases z with i|i; exact Or.inl ⟨i,mem_toLeft.mpr hp,hf⟩; exact Or.inr ⟨i,mem_toRight.mpr hp,hf⟩
      rintro (⟨z,h,hp⟩|⟨z,h,hp⟩); exact ⟨.inl z,mem_toLeft.mp h,hp⟩; exact ⟨.inr z,mem_toRight.mp h,hp⟩
   have he: ((edgesM S S' B).card:ℝ) ≤ S'.card*(Itinerary.density S.patch.L:ℝ):=by exact_mod_cast (lensRent (S:=S) S' B)
   apply he.trans; apply mul_le_mul_of_nonneg_right _ (by positivity)
   have hv: (S'.card:ℝ) ≤ (H.unionP u.toLeft).card+(∑ i∈u.toRight, ((Y.ground i).card:ℝ)):=by
     rw [hp]; exact_mod_cast ((card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le _))
   unfold worthX; rw [add_mul,sum_mul]; refine hv.trans (add_le_add (spaces ..) (sum_le_sum fun i _=>?_)); exact_mod_cast brood (Y.ground i) (radiusB s)
variable (F)
lemma gateL {a t:ℝ}{w:ι→ℝ}(hw:∀ i,0≤ w i)(hp: (unitsP Q L μ R.beta s C' a t).Buy S.patch.L Q.halo (radiusB s))(hv: Ac.Hit Y.ground (radiusB s) w Q.relative t) :
 let P':= unitsP Q L μ R.beta s C' a t
 Ready (Y.suitcase F).gP (radiusB s) (tariff (checkL Ξ w a t) ((Y.suitcase F).inks P' (fun _=>0)) (fun i=>P'.markSeed*(Y.suitcase F).tenants i) Q.ε) (P'.exponent+2*Q.ε) P'.rootHit P'.reserveTree P'.q:=by
   intro P'; let K:= Sum.elim H.birth Y.ground; let Z:=Sum.elim Ξ.flair w; let X:=Sum.elim (ConnectedActivityE6.lengths T R) (fun _:ι=>0); let B:=radiusB s
   have hx: Accounts S Q.halo B P' K Z X (steamP S P'):=by
     refine ⟨fun i _=> ⟨mul_nonneg hp.capture (Real.exp_pos _).le,le_rfl⟩,?_,?_,?_⟩
     · rintro (i|i); exact Ξ.accrues.holds i; exact hw i
     · rintro (i|i); exact Ξ.accrues.extra i; exact le_rfl
     intro i
     let U:=tariff w (fun _=>0) (fun _=>0) Q.ε
     have he: U=w:=by ext i; simp [U,tariff]
     convert! Labels.together _ _ _ Ξ.accrues.pays (he.symm ▸ hv) i using 1 -- name/options projection
     ext k
     rcases k with k|k <;> rfl
   have he:= Mixed.ready_vertices S Q.halo B P' _ _ _ _ hp hx
   let U:=shifts S ι
   refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.1, fun i=>he.2.2.2.2.1 (U i),fun i=>?_⟩
   convert! budget_pull U U.injective (he.2.2.2.2.2 i) using 1; ext j; rcases j with (i|i)|i<;>rfl
end YM.ConnectedActivityE6.Blaze.King
