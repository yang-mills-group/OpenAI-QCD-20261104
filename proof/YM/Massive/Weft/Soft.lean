import YM.Massive.Weft.Lift
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Weft
open Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y0: Code c N) -- independent shape
set_option quotPrecheck false
variable (Y:Ruby.Hue c N Ω)(X:Gem c N I)(Q:Ruby.Hue c N I)(K: ℝ)
variable {g:Site c→ℂ}(L':I→Dye)(L0:Ω→ Dye)
open Ruby
lemma mixesCost (he:SoftCost Y n v W t)(h:fareG 1 r N≤t)(hz:0<r): SoftCost (HGrace Y) n v W r:=by
   obtain ⟨f,hp,hQ⟩:=he; let N₀ i:= averageC c*f i
   refine ⟨N₀∘Prod.snd,fun x=>?_ ,?_⟩
   rotate_left
   · rintro ⟨v,i⟩ U; let A:= spice v (Y.mean i (Strut.sky v U)); change ‖token _ _ _ (averageC c • A)‖≤_
     have ht : token c N r (averageC c • A)=averageC c • token c N r A:=map_smul ((token c N r).restrictScalars ℝ) ..  -- wrong token vs songT defeq?
     rw [ht,norm_smul,Real.norm_of_nonneg (avPos _|>.le)]; exact mul_le_mul_of_nonneg_left (((soared v 0 t h hz _).2).trans (hQ _ _)) (avPos ..|>.le)
   let z(v:Strut c):=(act v).symm x; refine budget_rows _ _ (fun v=> ?_) (copiesG (c:=c) (budget_nonneg (hp 0))); convert! budget_scale (avPos c|>.le) (hp (z v)) using 1; ext i
   have he: x∈(HGrace Y).bud (v,i) ↔ z v∈Y.bud i:=by nth_rw 1 [← (act v).apply_symm_apply x]; change act v (z v)∈Finset.image (act v) (Y.bud i) ↔ _; simp
   rw [show coverNumber n ((HGrace Y).bud (v,i))=coverNumber n (Y.bud i) from cover_map (act v) (turn_sep _ _) ..]; by_cases h:x∈ (HGrace Y).bud (v,i)
   · rw [if_pos h, if_pos (he.mp h)]; exact mul_assoc ..
   rw [if_neg h,if_neg (mt he.mpr h),mul_zero]
lemma latest (u:ℝ)(hs:SoftCost Y n v W t)(he:u * r ≤ t)(hv:0<r)(hu:0<u): SoftCost (tiltT Y u) n v W r:=by
   obtain ⟨f,h,hp⟩:=hs; exact ⟨f,h,fun i U=>(quy _ _ _ _ hu hv he).trans (hp i U)⟩
structure CostTall (Y:Ruby.Hue c N Ω)(P:BudgetPoint)(t v w:ℝ)(X:Ω→Dye):Prop where
   tree: Y.Tall P.threshold
   paint: PatchH Y X
   budget: SoftCost Y P.B v w t

noncomputable def wet (Y:Ruby.Hue c N Ω)(v:Ω→ℂ): Ruby.Hue c N Ω:= ⟨Y.bud,fun i=> v i • Y.mean i⟩
lemma wetted (f:Ω→ℂ)(hp:Y.Tall t): (wet Y f).Tall t:=by
    refine ⟨fun i U V he h=> congr_arg (f i • ·) (hp.bond i U V he h), fun i=> measurable_const.smul (hp.meas i), fun i U hn=> hp.non i U fun hz=>hn ((congr_arg (f i • ·) hz).trans (smul_zero _)), fun i U=> ?_⟩
    unfold Cove.Gated; rw [show (wet Y f).mean i U=f i • Y.mean i U from rfl,map_smul]; exact Subalgebra.smul_mem _ (hp.lives ..) (f i)
lemma wetCost (f:Ω→ℂ)(h:∀ i,‖f i‖≤1)(hp:SoftCost Y n w W v): SoftCost (wet Y f) n w W v:=by
    obtain ⟨g,hg,hY⟩:=hp; refine ⟨g,hg,fun i U=>?_⟩; rw [show (wet Y f).mean i U=f i • Y.mean i U from rfl, J_of, map_smul,norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h i)).trans (hY i U)
lemma readable (F:ℝ)(U:Grid c)(he:Y.Tall F)(hs:SoftCost Y n v w t)(ht:0 ≤ v)(hp:1≤t): Summable (fun i=>Y.mean i U) ∧ Summable (fun i=> ‖Ruby.sparkY Y U i‖):= by obtain ⟨f,h,hY⟩:= hs; exact Ruby.hearts Y he h (fun i=>(norm_nonneg _).trans (hY i 1)) hp ht hY U
lemma teamed (U:Grid c)(x y: EvenA c N)(h:HasSum (fun i=>Q.mean i U) x)(hp: HasSum (fun i=>Y.mean i U) y): HasSum (fun i=>(Ruby.HJoin Q Y).mean i U) (x+y):= HasSum.sum (f:=fun i=>(Ruby.HJoin Q Y).mean i U) h hp
lemma couple {w':ℝ} (h:CostTall Y P t v w L0)(hp:CostTall Q P t v w' L') : CostTall (Ruby.HJoin Y Q) P t v (w+w') (Sum.elim L0 L'):=by
   obtain ⟨p,hp,hc⟩:= hp; obtain ⟨q,h,hY⟩:=h; refine ⟨Ruby.branche _ _ q p,?_,?_⟩ -- fill
   · refine ⟨?_,fun v k g hv=>?_⟩; · rintro (i|i); exact h.feel i; exact hp.feel i
     obtain ⟨U,hU,hV⟩:= h.turn v k g hv; obtain ⟨J,hJ,hT⟩:=hp.turn v k g hv; exact ⟨Equiv.sumCongr U J,fun i=>by cases i; exact hU _; exact hJ _, fun i=> by cases i; exact hV _; exact hT _⟩
   obtain ⟨f,hf,hR⟩:= hY; obtain ⟨g,hg,he⟩:=hc; refine ⟨Sum.elim f g,?_,fun i=>by cases i; exact hR _; exact he _⟩; exact fun i=> Extra.Iteration.Cost.sum (hf i) (hg i) -- name
end YM.QCD.Weft
