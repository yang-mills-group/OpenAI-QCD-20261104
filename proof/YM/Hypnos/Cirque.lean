import YM.Hypnos.Forelock
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}

-- actual aid for enclosures etc
variable (X:Coat T F)(Y: Support c)
lemma enact (h: Target.GrantBodies W X.x μ L Q o A T) (hx:X.width=o.K)(hf:X.manifest) {z:Air f G} (hc:Calm X Y o.ξ β z)(hβ:0<β) (B: Finset (Bond f))(he: ∀i∈B, atEdge S i∈Y) : X.enforce o.a (X.liftA β z) B=1 ∧ X.enforce (2*o.a) (X.liftA β z) B=1:=by
    obtain ⟨hσ,hγ,-,H⟩:= h.safety; obtain ⟨hm,hV⟩:= H F X rfl hx hf; have hr:=h.room.fiery
    have hp i (hi:i∈B) : X.cone o.a (X.liftA β z) i=1 := by
       apply X.premiere (mul_pos o.large hr); change ‖X.μ i+gStep β • X.atmos z i‖ ≤ _
       exact (norm_add_le ..).trans ((add_le_add (hm _) (calm_bonds X Y h hx hf hc hβ i (he _ hi))).trans ((le_of_eq (by ring : _ = (o.cap+1)*X.t)).trans (mul_le_mul_of_nonneg_right hγ hr.le)))
    exact ⟨Finset.prod_eq_one hp, Finset.prod_eq_one (fun i hi=> X.serves (mul_pos o.large hr) _ _ (hp i hi |>.trans_ne one_ne_zero))⟩

lemma calmSet (ξ β:ℝ): MeasurableSet {z| Calm X Y ξ β z}:=by
    unfold Calm Coat.watch; simp only [Set.setOf_forall]; apply Y.measurableSet_biInter; intro i hi; apply MeasurableSet.iInter; intro j; apply MeasurableSet.iInter; intro h; exact measurableSet_le (show Continuous fun z:Air f G=>|z j| by fun_prop).measurable measurable_const
private def cry (S:StepData c f)(i:Site c) : WarningAt c f:= .inl (.inr (.inr (.inr (.inl i))))
lemma modest (ξ β:ℝ)(v:ℝ)(h: ∀ i:WarningAt c f,X.dice.real (X.catastrophe ξ β {i}) ≤ v): X.dice.real {z|¬Calm X Y ξ β z}≤ Y.card*v:=by
    let f i:= X.catastrophe ξ β {cry S i}
    refine ((measureReal_mono (show {z | ¬Calm X Y ξ β z}⊆⋃ i∈ Y,f i from ?_) (measure_ne_top _ _)).trans (MeasureTheory.measureReal_biUnion_finset_le ..)).trans ((sum_le_sum (g:=fun _=>v) (fun i _=>h _)).trans_eq (by simp))
    intro p hp; change ¬ ∀ i∈Y,X.watch i ξ β X.B p at hp; push Not at hp; obtain ⟨i,hv,hp⟩:=hp
    refine Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hv,?_⟩⟩; unfold f catastrophe; intro j hj; rw [mem_singleton.mp hj]; unfold watch at hp; push Not at hp; obtain ⟨k,hk,hb⟩:= hp; exact ⟨_,hk.trans (show X.B≤2*X.B by omega),hb.le⟩
-- spool under V charts
lemma vein_temp (G:Gauge)(L:Side) : Rate G L (-(1/2)) temp:=by
    let Y:= Rate.flame (G:=G) (L:=L); refine Rate.compare (Y.mul_left 2) ?_
    let z := G.slopeConstant * Real.log L.val
    filter_upwards [Work.E04.eventually_temp_le z (Work.E04.shift_nonneg G L)] with x hx
    rw [abs_of_nonneg (Work.E04.temp_nonneg x)]; exact hx.trans (le_abs_self _)
open Planned.AtomRegular.Foliage
lemma windA (G:Gauge)(L:Side)(m:ℕ) : ∃ V:ℝ→ℝ, Rate G L (-(1/2)) V ∧ ∀ᶠ x:ℝ in atTop, 0≤ V x ∧ ∀ (c:Side)(i : Site c)(U:Config G c)(Y:Support c)(n:ℕ), n ≤ m*radiusB x→ Healthy (temp x) Y U → halo (n+1) {i}⊆Y → 2*(n+1)<c.val → ∃ g: Site c→ G.El, ∃ b:Directions G c, ‖b‖≤V x ∧ AgreeNear id i n (gauge g U) (increment 1 b):=by
    obtain ⟨C,d,hC,hd,h⟩:= log_chart_cost G
    let r x:= (m* radiusB x:ℕ); let Z (x:ℝ):= 4*(temp x*(1+(r x:ℝ))); have hZ : Rate G L (-(1/2)) Z:=by
       have hh:Rate G L 0 (fun x=>(r x:ℝ)):=by unfold r; push_cast; exact Rate.radius_price.mul_left m
       simpa only [add_zero] using ((vein_temp G L).mul ((Rate.const 1).add hh)).mul_left 4
    refine ⟨_,hZ.mul_left C,?_⟩
    filter_upwards [hZ.below (by norm_num) d hd] with x hx
    have hp:=Work.E04.temp_nonneg x; have hs : 0 ≤ Z x:=by unfold Z; positivity
    refine ⟨mul_nonneg hC.le hs, ?_⟩; intro c i U Y n he hv hY hc; obtain ⟨g,hg⟩:=Cube.anchored i hv hp hY hc
    let b:=PhysicalNext.JointLoad.Heir.crop i n g U
    have ht (a: Bond c) (ht: separation i a.1 ≤ n): G.chord (gauge g U a)≤ Z x := (hg a ht).trans (by unfold Z; gcongr; exact ht.trans he)
    refine ⟨g,b,?_,?_⟩
    · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le hs)).mpr fun j=> ?_; unfold b JointLoad.Heir.crop; split
      next he => exact (h _ ((ht _ he).trans ((le_abs_self _).trans hx))).2.trans (mul_le_mul_of_nonneg_left (ht _ he) hC.le)
      rw [norm_zero]; positivity
    intro a hq; change separation i a.1≤n at hq
    rw [increment]; unfold b JointLoad.Heir.crop; rw [if_pos hq,(h _ ((ht a hq).trans ((le_abs_self _).trans hx))).1,Pi.one_apply,mul_one]

-- affection: roof obligations H.Photic ∀ v choices under schedule if needed.
structure Peace (W μ x A u r d v :ℝ)(G:Gauge) (P:Teller G)(o:ConnectedActivityE6.Target.Order G W) (Q:ConnectedActivityE6.Target G P) (L:Side) (Pi₀:Patch)(X:State G):Prop where
    glow : r ≤ X.r
    spells : ∀ (c f:Side) (S:StepData c f)(T:Tube G S) (F:Forest S.ratio), S.patch=Pi₀ → Target.GrantBodies W x μ L Q o A T → Stamp T →
       ∀ (Z:Coat T F), Z.x=x → Z.width=o.K→Z.manifest→∀ (Y:Support c)(b:Directions G c), ‖b‖≤u →Z.V=increment 1 b → (∀ i∈Y,¬Inside i Z.seeds (30*Z.B))→
       (∀ H:Bed, Attached H T.up→ Sworn H f G →(H.full T.high f).transpose*H.full T.high f=H.metric.acts f →
         ∀ (i j: Star F G),S.ratio.parent j.1.val.1∈Y→|Z.relating (i.1.val,i.2) (j.1.val,j.2)-(FreeResolvent.treeMatrix G S F H.metric)⁻¹ i j|≤v) ∧
       ∀ (R: Rep G f), Intake P T x R→∀ z:Air f G, Calm Z Y o.ξ R.beta z→HaloV Z Y R.beta r d b z
lemma cartSigns (G:Gauge)(P:Teller G)(o:Target.Order G W)(Q:ConnectedActivityE6.Target G P)(Pi₀:Patch)(L:Side)(X:State G)(V:ℝ→ℝ)(hD:Pi₀.Branches P.bind G)(hV:Rate G L (-(1/2)) V)(hp:∀ᶠ x in atTop,0≤V x) (μ A : ℝ):
    ∃ (U D E :ℝ → ℝ), Rate G L (-(1/2)) U ∧ Rate G L (-1) D ∧ Rate G L (-(1/2)) E ∧ ∀ᶠ x in atTop, Peace W μ x A (V x) (U x) (D x) (E x) G P o Q L Pi₀ X :=by
    obtain ⟨r,Z,hr,hZ,h⟩:= JointLoad.Heir.orchestra G Pi₀ P hD 2 le_rfl
    obtain ⟨t,C,ht,hC,hM⟩:=Malachite.treasure G P L Pi₀ hD 2 le_rfl hV hp (-(1/2))
    obtain ⟨M,hH,hm⟩:=budget_expandBare G; obtain ⟨K,hk,H⟩:= polarized G P L Pi₀ (-(1/2))
    let s x:= M*(C x*(t x+V x)*V x); let v x:= V x+ (fiery G x L+s x); let d x:=Z*v x; let U x:= Z*(temp x+v x)*v x+s x
    have hw:Rate G L (-1) s:=by convert (((hC.mul (ht.add hV)).mul hV).mul_left M) using 1; norm_num
    have hv:Rate G L (-(1/2)) v:= hV.add (Rate.flame.add (hw.weaken (by norm_num))); have he :Rate G L (-(1/2)) (fun x=> C x*V x):= by simpa only [zero_add] using hC.mul hV
    have hd:=hv.mul_left Z
    have hu: Rate G L (-1) U:=by refine Rate.add ?_ hw; convert ((((vein_temp G L).add hv).mul_left Z).mul hv) using 1; norm_num
    refine ⟨d,U,fun x=>C x*V x+t x+K x,hd,hu,(he.add ht).add hk,?_⟩
    filter_upwards [h,hM,H,hp,hv.below (by norm_num) _ hr, hd.below (by norm_num) _ X.r_pos] with x hx hy h H' hv hd'
    -- t,C ≥0? hy only for authorized when Coat. Peace.glow demands unconditional. choose abs prices!
    constructor -- later if fails
    · exact (le_abs_self _).trans hd'
    intro c f S T F hh hT hS Z ht' hu' hP Y b hz hb hq; subst x
    obtain ⟨hM,hC,hQ⟩:=hy _ _ S T hh hT.funds F Z rfl;
    refine ⟨fun B hA hW hF _ j hj=> enlightened Z Y (h _ _ hh hT.funds _ hA hF hW _ Z rfl) hQ _ hz hb hT.room hq _ _ hj,fun R hI z he=>?_⟩
    unfold U d v s; rw [← hT.funds.length_eq]; refine fought Z Y hT hu' hP he hI.positive b hz hQ (hm S F Z.x) (hx S T hh (booths hS hT.funds.funds) hT.room.buys F Z.k) ?_ hq hb
    unfold Coat.t; rw [hT.funds.length_eq]; exact (le_abs_self _).trans hv
end YM.Hypnos
#print axioms YM.Hypnos.cartSigns
#print axioms YM.Hypnos.windA
