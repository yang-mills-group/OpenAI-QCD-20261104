import YM.QCD.House.Contract

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
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
set_option quotPrecheck false
local notation "B"=>radiusB τ
variable {z α b γ d θ:ℝ}
def barley (b:Costs):ℝ:= (1+2*Real.exp 1)* apple b
def crownQ (L: Side)(θ μ C x a β:ℝ)(Q:Target su P):=Pipe.unitsP Q L μ β x C a (Loom.demandQ L θ x)
lemma blastR {L:Side}(ht:0<μ)(hx:0<θ)(Q:Target su P): Rate su L (max Q.rate (-(3/8:ℝ))) (fun x=> apple (crownQ L θ μ C x 0 0 Q)):=by
   let e:= max Q.rate (-(3/8:ℝ))
   have h:Rate su L e (Q.goal L):= Rate.power.weaken (le_max_left ..)
   have hh:Rate su L e (fun x=> Real.exp (-Delay.hatWin su L (μ/2) (1/2) x /4)) := by
       let v:= μ/16; have he: Rate su L e (fun x=> Real.exp (-v * (Delay.fineMonitor su L x ^ (2:ℝ)))):= Rate.monitor_cutoff (by unfold v; positivity) (by norm_num)
       refine he.congr (Eventually.of_forall fun x=>?_); unfold Delay.hatWin; simp only [Real.rpow_two]; unfold v; apply congr_arg; ring
   exact (hh.add (h.add ((cunning L θ hx).1.weaken (le_max_right ..)))).mul_right ((1-1/2:ℝ)⁻¹)
structure Corner (Q:Target su P)(l:ℕ)(b:Costs)(z:ℝ):Prop where
 exp : 0 ≤ z
 used : z+1+1 ≤ b.exponent
 directs : 0 < apple b
 adds : degreePrice l (apple b) 1≤1/2
 radial : degreePrice l (barley b) 1≤1/2
 success : apple b*(1-(1/2:ℝ))⁻¹≤1
 ban : barley b*(1-(1/2:ℝ))⁻¹≤1
include Q in
lemma afterK (L:Side)(M θ:ℝ)(ht:0<M)(he:0<θ)(hz:0≤ α)(hv:α+1+1 ≤ Q.exp): ∀ᶠ x in atTop,∀ a C:ℝ,∀ β:ℝ, Corner Q (radiusB x) (crownQ L θ M C x a β Q) α:=by
   have hr:= Q.stop; have hh : max Q.rate (-(3/8:ℝ))<0:= max_lt hr (by norm_num)
   let d x:= crownQ L θ M 0 x 0 0 Q; have h:= blastR (C:=0) (L:=L) ht he Q; let s:=fun x=> apple (d x)
   have hb:= h.mul_left (1+2*Real.exp 1); let H:=fun x=> barley (d x); have hb:Rate su L (max Q.rate (-(3/8:ℝ))) H:=hb
   have hzQ (g:ℝ→ℝ)(hg:Rate su L (max Q.rate (-(3/8:ℝ))) g): Rate su L (max Q.rate (-(3/8:ℝ))) (fun i => degreePrice (radiusB i) (g i) 1):=by
      have hh := Census.width_rate su L 1 0; simp only [one_mul,add_zero] at hh; -- check constant
      unfold degreePrice Trees.stretch; simp only [div_one]; simpa only [zero_add] using! (hh.mul hg).mul_left 4
   filter_upwards [Delay.shift_pos su L,(cunning L θ he).2, (hzQ s h).below hh (1/2) (by norm_num),(hzQ H hb).below hh (1/2) (by norm_num),(h.mul_right ((1-(1/2:ℝ))⁻¹)).below hh 1 (by norm_num),(hb.mul_right ((1-(1/2:ℝ))⁻¹)).below hh 1 (by norm_num)] with x hV hp h1 h2 h3 h4 a C β
   refine ⟨hz,hv,?_,(le_abs_self _).trans h1,(le_abs_self _).trans h2,(le_abs_self _).trans h3,(le_abs_self _).trans h4⟩
   unfold apple Costs.rootHit crownQ Pipe.unitsP Buy.quote Target.goal -- edit
   simp only; positivity -- edit
-- Faber exact final map.
variable {w: Reserve S→ι→ℝ}{p:ι→ℝ}{c₀:Costs}{ν:ℝ}
lemma fuel (X:Y.Faber) :(sweep Y.invD X.val).Nonempty ∧ sweep Y.invD X.val ⊆ wound Y.broad X.val:=by
    constructor
    · obtain ⟨i,hi⟩:= X.2.1; obtain ⟨j,hj⟩:= i.2.2; exact ⟨j,mem_biUnion.mpr ⟨_,hi,hj⟩⟩
    intro i hi; obtain ⟨j,hj,h⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨.inl j, mem_toLeft.mp hj,Y.bookD j h⟩
def ket (χ:Chi)(V:Grid c)(s:Finset Y.Faber): EvenA c N := if (s:Set Y.Faber).PairwiseDisjoint (fun i=> wound Y.broad i.val) ∧ (s.biUnion (fun i=>GasP.sweep Y.invD i.val))= RG.flags (Pressure.temp τ) V then ∏ i∈s,Y.mission χ V i.val else 0
lemma carriesC (χ:Chi)(V:Grid c)(t:Finset Y.Faber): Y.ket χ V t= GasP.ward Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) V) (duskV Y χ V) (dawnV Y χ V) (t.image Subtype.val):=by
    unfold ket ward; refine if_congr (and_congr ?_ ?_) ((prod_image Subtype.val_injective.injOn).symm) rfl
    · refine ⟨fun p=> ⟨fun i hi=>by obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact j.2,?_⟩,?_⟩
      · intro i hi j hj hn; obtain ⟨i,h1,rfl⟩:=mem_image.mp hi; obtain ⟨j,h2,rfl⟩:=mem_image.mp hj; exact p h1 h2 (fun h=>hn (h ▸ rfl))
      intro p i hi j hj hh; exact p.2 (mem_image_of_mem Subtype.val hi) (mem_image_of_mem Subtype.val hj) (fun h=> hh (Subtype.ext h))
    rw [wing_cost,image_biUnion]
lemma beck (hf:Y.Famous)(hp:Y.Feasible)(ht: Y.Leaps w c₀ p α)(h: Corner Q (radiusB τ) c₀ z) (hh:0<α) (χ:Chi)(V:Grid c): Summable (honest Y χ V) ∧ Summable (ket Y χ V) ∧ HasSum (fun i=>Y.emergingF i χ V) (NormedSpace.exp (∑' i,honest Y χ V i) *∑' i,ket Y χ V i) ∧ let P (i:Y.Wort):=tenderW Y.broad Y.lightF i (fun j=>Y.grass w c₀ j.val) (fun j=>Y.grass w c₀ j.val)
    (∀ u:Y.Faber, ‖token c N α (Y.mission χ V u.val)‖≤P u.val) ∧ Ac.Hit (fun i:Y.Faber=> GasP.wound Y.broad i.val) (radiusB τ) (taxed (fun i:Y.Faber=> GasP.sweep Y.invD i.val) (fun i=> P i.val) (Real.exp c₀.markSeed)) z 1:=by
   have hR:z+1≤ c₀.exponent:=(le_add_of_nonneg_right zero_le_one).trans h.used
   have hv:0<barley c₀:=mul_pos (by positivity) h.directs
   have hu : apple c₀+Real.exp 1*(apple c₀*(1-1/2)⁻¹) ≤ barley c₀:= le_of_eq (by unfold barley; ring)
   obtain ⟨h1,h2,h3,h4,h5⟩:= awardW Y ht hp hf hh h.exp zero_lt_one hR (ceremony Y ht (by linarith [h.exp] : 0 ≤ z+1) h.used zero_lt_one h.directs h.adds (by norm_num)) h.radial hv (by norm_num) h.success hu χ V
   let W:= ward Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) V) (duskV Y χ V) (dawnV Y χ V); let f (s: Finset Y.Faber):=s.image Subtype.val
   have he:Injective f:= Finset.image_injective Subtype.val_injective
   have hQ : Y.ket χ V=W ∘ f := funext (carriesC Y χ V)
   have he': Function.support W ⊆ Set.range f:=by -- edit
      intro i hi; change W i≠0 at hi; unfold W ward at hi; split at hi
      next hs=>
          let A:=i.preimage Subtype.val (Subtype.val_injective (p:=fun i=> wagon Y.broad i)).injOn; refine ⟨A, Finset.ext fun v=>?_⟩
          constructor
          · intro h; obtain ⟨v,hv,rfl⟩:=mem_image.mp h; exact mem_preimage.mp hv
          intro hv; exact mem_image.mpr ⟨⟨v,hs.1.1 v hv⟩,mem_preimage.mpr hv,rfl⟩
      next h=> exact False.elim (hi rfl)
   refine ⟨h1, hQ.symm ▸ h2.comp_injective he, ?_,fun i=>h4 i.1,fun i=> budget_loosen (budget_pull Subtype.val Subtype.val_injective (h5 i)) h.ban⟩
   rw [hQ]; have hx : (∑' i, (W ∘ f) i)= ∑' i,W i := he.tsum_eq he'; rw [hx]; exact h3
end YM.QCD.Loom.Fleet
