import YM.QCD.Golden.Rose
/-! # Meristem progeny on Drivable to output E6 lit. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {Ñ : ChartRatio G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E}
variable {z : Air f G} (H : Cash W s μ L Q o C T R) (hX : X.x=s) (hM : X.manifest) (hK : X.width=o.K)
variable (hq : Glass P X V x j W) (hC : Canary G A b) (he : 8*o.a*Pressure.fiery G s L ≤ A/2)

include H hX hM hK hq hC he
lemma rhythmsM (p : Molecule S) (I : Finset (Bond f)) :
    let m:=(F.order G).prod X.dice; let g v:= rhythm I X (V v) A Q.table p R W o.a Q.halo
    ∃ B : _→ℝ, Integrable B m ∧ ∀ᶠ y in 𝓝 x, ∀ i, Brush j (B i) 1 (fun y=> g y i) y := by
  intro m g
  have heq:=H.laws.data; have hv := heq.funds.length_eq; rw [← hv,← hX] at he
  have hM :=heq.localP F X hX hK hM
  have ht:= (hX.symm ▸ H.laws.intake : Intake P T X.x R); have hh: ShellAccess S G X.x W X.width o.γ := by rw [hK,hX]; exact heq.access
  let A' := lensS I G; let U i:=circuit A' (vary X (V i)).relating; let V':= circuit A' X.relating
  have hx: U x=V' := by unfold U V'; rw [hq.lifts]; rfl
  have hF:= hM.sails.fullC; have hU' : V'.PosDef := hF.submatrix Subtype.val_injective
  have hV:= own_mat hM.sails I
  have hs : Bottom V'⁻¹ (1+payE o.eta o.gap o.ample (tubularPrice G L))⁻¹ := Control.lower_inverse hV.relented hV.weather.1.le hV.fuel hV.symmetry
    hV.ground hV.down.le hV.initial.1
  let X'(t:F.Slice G × Air f G):= X.wrapY t.1; let w t v:= course (X' t) A R.beta t.2 (V v)
  let z(t:F.Slice G×Air f G):= Pond.swim A' t.2; have hZ : MeasurePreserving z m (sweep V') := by
    have hs := (Pond.orbit hF.posSemidef A')
    apply hs.comp (show MeasurePreserving _ m X.dice from _); exact MeasureTheory.measurePreserving_snd
  let Z t i:= Pond.swim A' (w t i)
  obtain ⟨hΞ,hω⟩:= Glass.towers (U:=fun i:F.Slice G × Air f G=> i.2) (Y:=fun i=> i.1) hq hM.sails.room hC I ht.positive
  obtain ⟨B,hB,hk,hP⟩:= winglet (A:=U) (Z:=z) (V:=Z) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>hq.relate i.val j.val) hω
  let Φ i v:= Polar.floating (vary (X' i) (V v)) o.a R W Q.table (w i v) (own p) Q.halo p
  have ht': 4*o.a*X.t < Q.table.radius := by
    have ht:=heq.covers; rw [← hv, ← hX] at ht; exact ht
  have hΨ : Zest Φ x j := hq.thorn (Y:=Prod.fst) Prod.snd hM.sails.room hC ht p Q.halo Q.table_exists
    (mul_pos o.large hM.sails.room.fiery) he ht'
  obtain ⟨J,hJ,hH⟩:= hΞ.post
  obtain ⟨K,h₁,h₂⟩:=hΨ.post
  let K' t:=(J*B (z t)*K)*(1+((1+1)+1))^j
  rw [hx] at hk
  have hb : Integrable (B ∘ z) m := (hZ.integrable_comp hB.aestronglyMeasurable).2 hk
  refine ⟨K',((hb.const_mul J).mul_const K).mul_const _,?_⟩
  filter_upwards [hH,h₂,hP] with i hi h hh s
  have hx' := hh s
  -- convert density origin
  rw [hx] at hx'
  exact (((hi s).paints hx').paints (h s)).trim
end YM.ConnectedActivityE6.Blaze.Flux
namespace YM.ConnectedActivityE6.Blaze.Golden
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (h:Y.Famous)(he:Canary su d A)
-- Frozen formula for price motion all z. Works weighed V have no U glue.
def husks (i:ι)(W:Coat T F)(v:Directions su f)(C:Config su f):= W.enforce (2*o.a) v (W.plaza (Y.window i)) • Y.works i C W.V
include h he
lemma pulp (X:Coat T F)(s':Air f su)(i:ι)(U:Config su c)(hp:Drivable X d A U)(hX:0<o.a*X.t)(hh:8*o.a*X.t≤d/2): let V':= vary X U; let u:= worldZ X R.beta s'; let v:= steer X d u U; let w:= steer X d (fun i=> prune d (u i)) U
    Y.muscle i V' (course X d R.beta s' U)= husks Y i V' v (X.input u) ∧ husks Y i V' v (X.input u)=husks Y i V' w (X.input u):=by
   intro V' u v w; have hV := plastic (X:=V') (conquered X he U u hp hX hh) (show 0<o.a*V'.t from hX); have hv:Transfer V' v w (4*o.a*X.t):= ⟨(fruit X he U u (a:=4*o.a*X.t) (by nlinarith only [hh,he.warm])).both⟩
   refine ⟨?_,?_⟩
   · unfold muscle; rw [Silica.proceeds X d H.laws.intake.positive]
     let p:= V'.plaza (Y.window i); let t':= V'.enforce (2*o.a) v p
     change t' • Y.works i (V'.input v) U=t' • Y.works i (X.input u) U
     by_cases he:t'=0
     · rw [he,zero_smul,zero_smul]
     exact congr_arg _ (h.locally i U _ _ fun j hj _=> hV.heading _ he j (h.horizons i (mem_image_of_mem _ hj)))
   exact congr_arg₂ (fun (r:ℝ)(u:EvenA c N)=>r • u) (prod_congr rfl fun i _=> (Transfer.grain V' hv hX i (2*o.a) (by rw [mul_assoc]; exact mul_pos (by norm_num) hX) le_rfl).1) rfl
variable (X:Coat T F) (D:Glass P X V x j W)
include D
lemma floatingX (hv:0<o.a*X.t)(hh:8*o.a*X.t ≤ d/2)(I:ι) (hS: Zest (fun (U: Config su f) t=>Y.works I U (V t)) x j):
   Zest (fun (t:F.Slice su ×Air f su) i=> Y.muscle I (vary (X.wrapY t.1) (V i)) (course (X.wrapY t.1) d R.beta t.2 (V i))) x j :=by
    let A (t:F.Slice su ×Air f su):=X.wrapY t.1; let Z t i:= vary (A t) (V i); let Q t:=worldZ (A t) R.beta (Prod.snd t); let w t i:= steer (A t) d (fun j=>prune d (Q t j)) (V i); let p t:= (A t).input (Q t)
    have hQ:Zest w x j:=(D.foreshadow (Y:=Prod.fst) Q he).1
    let g t i:= X.enforce (2*o.a) (w t i) (X.plaza (Y.window I))
    have hf: Zest g x j:=Zest.full (X.plaza (Y.window I)) _ (fun i _=> (hQ.replay (ContinuousLinearMap.proj _)).wand (Glass.tip (X:=X) _))
    apply ((hf.pair (hS.via p)).wand (p:=fun z:ℝ×EvenA c N=> z.1 • z.2) (by fun_prop)).congr
    obtain ⟨c,hv'⟩:=D.sails; filter_upwards [nearby X he D.lifts hv'] with y hy t; have ht:Drivable (A t) d _ (V y):=⟨hy.good⟩
    have hh':= pulp Y h he (A t) t.2 I (V y) ht hv hh; exact (hh'.1.trans hh'.2).symm
omit h he D
lemma brushA {a b: E→EvenA c N}{w v e t:ℝ}(hp:Brush j w e a x)(hg:Brush j v t b x): Brush j (w*v) (e+t) (fun u=> a u*b u) x:=paints hp hg
lemma brushR {a:E→ℝ}{b:E→EvenA c N}{w v e t:ℝ}(hp:Brush j w e a x)(hg:Brush j v t b x): Brush j (w*v) (e+t) (fun u=> a u • b u) x:=by
   let L:=algebraMap ℝ (EvenA c N); let S : ℝ →L[ℝ] EvenA c N:= (ContinuousLinearMap.id ℝ ℝ).smulRight (1:EvenA c N);
   have ht': ‖S‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by change ‖i • (1:EvenA c N)‖ ≤ _; rw [norm_smul,norm_one,mul_one,one_mul]
   have hx := hp.report S ht'; rw [one_mul] at hx
   apply (paints hx hg).shimmy; exact Eventually.of_forall fun i=> (show a i • b i=(a i • (1:EvenA c N))* b i by rw [smul_mul_assoc,one_mul])
lemma zing {P:Type} (J:Finset ι)(u:ι→ P→ E→EvenA c N)(hp:∀ i∈J,Zest (u i) x j): Zest (fun p y=>∏i∈J,u i p y) x j:=by
   induction J using Finset.induction_on with
   | empty=> simpa only [prod_empty] using Zest.still (A:=P) (x:=x) (k:=j) (1:EvenA c N)
   | insert i t hi he=> simp_rw [Finset.prod_insert hi]; apply ((hp _ (mem_insert_self ..)).pair (he fun j hj=> hp _ (mem_insert_of_mem hj))).wand (p:=fun z: EvenA c N × EvenA c N=> z.1*z.2); fun_prop
lemma meritX {P:Type}[MeasurableSpace P](U:E→P→EvenA c N)(m:Measure P)(h : ∃ B : P→ℝ, Integrable B m ∧ ∀ᶠ y in 𝓝 x, ∀ i, Brush j (B i) 1 (fun y=> U y i) y)
    (hM : ∀ᶠ y in 𝓝 x, Measurable (U y)) : Meristem U x m j ∧ ∀ᶠ y in 𝓝 x, Integrable (U y) m := by
  obtain ⟨B,hF,hP⟩:=h
  constructor
  · obtain ⟨O,hS,hO,hx⟩:= _root_.mem_nhds_iff.mp (hP.and hM)
    have ht (i:E) (hi:i∈O) : (∀ v, Brush j (B v) 1 (fun t=>U t v) i) ∧ Measurable (U i) := hS hi
    refine ⟨O,hO.mem_nhds hx,ae_of_all _ (fun _ t h=>(ht t h).1 _ |>.1),fun k hk=> ⟨B,hF,fun y hy=> ?_,ae_of_all _ fun i y hy=>?_⟩⟩
    · exact (Meristem.legs (f:=Function.swap U) hO (fun i t h=> ((ht t h).1 i).smooth) (fun i hi=> ((ht i hi).2.stronglyMeasurable)) hk hy).aestronglyMeasurable
    exact (Brush.offer.1 ((ht _ hy).1 i)).inside k hk
  filter_upwards [hP,hM] with t hp ht; exact hF.mono' ht.aestronglyMeasurable (ae_of_all _ fun i=> (hp i).bound)
include D h he
lemma icefall (hz:Y.speaking)(hX:X.x=s)(hp:X.width=o.K) (hx:X.manifest) (hh:8*o.a*Pressure.fiery su s L ≤ d/2)(J:Finset (Bond f))(u:I')(hr:∀ i∈u.toRight, Zest (fun (U: Config su f) t=>Y.works i U (V t)) x j):
 let m:=(F.order su).prod X.dice; let g t:=playM Y J d u X (V t); Meristem g x m j∧ ∀ᶠ y in 𝓝 x,Integrable (g y) m :=by
   intro m g; let C i a:= rhythm J X (V i) d Q.table u.toLeft R W o.a Q.halo a
   have hM:Meristem C x m j:= (boosts H hX hx hp D he hh u.toLeft J).1
   let U (t:F.Slice su ×Air f su) i :=∏ k∈u.toRight,Y.muscle k (vary (X.wrapY t.1) (V i)) (course (X.wrapY t.1) d R.beta t.2 (V i))
   have hV : X.t=Pressure.fiery su s L:=by unfold Coat.t; rw [hX,H.laws.data.funds.length_eq]
   have h₁:0<o.a*X.t:= mul_pos o.large (show 0<X.t from (hX.symm ▸ H.laws.data.room).fiery)
   have hg: Zest U x j:= zing u.toRight _ (fun i hi=> floatingX Y h he X D h₁ (hV ▸ hh) i (hr i hi))
   -- Meristem supply for componentwise NOT all: use ae. cannot meritX all. build directly.
   obtain ⟨M,hB,hF⟩:=hg.post
   have hy: ∀ᶠ y in 𝓝 x, Measurable (g y):= by obtain ⟨σ,hs⟩:=D.sails; filter_upwards [nearby X he D.lifts hs] with y hy; exact nectar Y X hz hX hp (V y) he hy u J
   -- use all fact for rhythm sharpen via Mercury proof rewrapped for all. proved boosts only ae. Need all leaf meas via meristem weaken. Easier recover Rhythm all from comparable lemma Golden.
   obtain ⟨T₀,hT,h⟩:= rhythmsM H hX hx hp D he hh u.toLeft J
   refine meritX _ _ ⟨fun u=> T₀ u*M*(1+(1+1):ℝ)^j,(hT.mul_const M).mul_const _,?_⟩ hy
   filter_upwards [h,hF] with y hy hY a; have hS := (brushR (hy a) (hY a)).trim
   exact hS.shimmy (Eventually.of_forall fun i=> (show g i a=C i a • (U a i) from (mul_smul ..).symm))
end YM.ConnectedActivityE6.Blaze.Golden
