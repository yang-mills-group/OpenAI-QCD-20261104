import YM.QCD.Golden.Germ
/-! # moving a reading through arbitrary lens -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Golden
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {β:ℝ} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (J:Finset (Bond f))(d:ℝ)
-- helper Float with Ember term occ cuts
abbrev cactus (u:I')(Z:Coat T F) (w:Air f su):= floating Z o.a R W Q.table w (own u.toLeft) Q.halo u.toLeft • ∏ i∈u.toRight,Y.muscle i Z w
def arts (u:I')(X:Coat T F)(V:Config su c) (z:Air f su): EvenA c N := scalp J X V R.beta d z • cactus Y u (vary X V) (course X d R.beta z V)
def playM (u:I')(X:Coat T F)(V:Config su c)(z:F.Slice su ×Air f su):= arts Y J d u (X.wrapY z.1) V z.2
variable {d J}(X:Coat T F)
lemma nectar (p:Y.speaking)(hv:X.x=s)(hk:X.width=o.K)(V:Config su c)(h:Canary su d A)(hp:Drivable X d A V)(u:I')(J:Finset (Bond f)):Measurable (playM Y J d u X V):=by
    have ht:Intake P T X.x R:= hv.symm ▸ H.laws.intake; have hz:ShellAccess S su X.x W X.width o.γ:=by rw [hv,hk]; exact H.laws.data.access
    let D:=F.Slice su×Air f su; let f (i:D):=X.wrapY i.1; let v' i:=(vary (f i) V); let z (i:D):= course (f i) d R.beta i.2 V; let s' (i:D) :=worldZ (v' i) R.beta (z i)
    obtain ⟨he,hh⟩:= steering J X h V hp (Y:=Prod.fst) (z:=Prod.snd) measurable_fst measurable_snd ht.ready hz R.beta
    have hZ:Measurable s':=(compassBro ht.ready (V:=fun _:D=> V) measurable_const X measurable_fst hz R.beta).2.2 z hh
    have he:Measurable (fun i:D=> Polar.floating (v' i) o.a R W Q.table (z i) (own u.toLeft) Q.halo u.toLeft) := collectionB X hz ht Q.table_exists (V:=fun x:D=>V) measurable_const measurable_fst hh ..
    let g (i:D):= rhythm J X V d Q.table u.toLeft R W o.a Q.halo i; have hf : Measurable g:= inshore (Y:=Prod.fst) (z:=Prod.snd) J X h V hp measurable_fst measurable_snd ht hz Q.table_exists _
    have hc j: Measurable fun i:D=> Y.muscle j (v' i) (z i):=( (X.enforce_b _ (X.plaza (Y.window j))).comp hZ).smul ((p j).comp (((Art.entering X (V:=fun _:D=>V) measurable_const measurable_fst hZ)).prodMk measurable_const))
    rw [show playM Y J d u X V= fun i=>g i • ∏ j∈u.toRight, Y.muscle j (v' i) (z i) from funext fun i=> (mul_smul ..).symm]
    exact hf.smul (Finset.measurable_fun_prod _ fun i _=> hc i)
-- Guard U invariance locality pure; lifting with nonmer extension uses older/silence
set_option maxHeartbeats 350000 in
lemma transitS (h:Y.Famous)(hx:X.x=s)(u:I')(v w:Air f su)(hp:Pond.swim (podium S su (Y.fullA u) (radiusB s)) v=Pond.swim (podium S su (Y.fullA u) (radiusB s)) w): cactus Y u X v=cactus Y u X w :=by
    let D:=Y.fullA u; let k:=own u.toLeft
    have hB:Borough X X D v w k k R:=⟨Village.refl ..,fun i hi=> (observe _).1 hp i (by change i∈podium S su D (radiusB X.x) at hi; rwa [hx] at hi),fun _ _=>Iff.rfl⟩
    have hH:Room P S T X.x:=hx.symm ▸ H.laws.data.room
    apply congr_arg₂ (fun (r:ℝ)(u: EvenA c N)=> r • u) (hB.flops hH Q.buys (hx.symm ▸ H.laws.intake) _ _ _ (by unfold Coat.B; rw [hx]; exact (Y.suitcase F).lesserP u))
    apply prod_congr rfl; intro i hi; rw [older,older]; apply buds Y i h X X _ _ hx (Village.refl ..); exact (observe _).2 (fun j hj=> (hB.rooms hH R.beta).airs j (mem_filter.mpr ⟨mem_univ _,fun k hk=>(Y.suitcase F).leP u hi ((mem_filter.mp hj).2 _ hk)⟩))
open scoped ENNReal
lemma rake (J:Finset (Bond f)) (h:Canary su d A)(V:Config su c)(hp:Drivable X d A V)(hB:0<β)(p: Poll.Body (↥(lensS J su)) → EvenA c N): (∫ t,p t)=∫ t,jacL J X d β V (Pond.spill (lensS J su) t) • p (pitch J X d β V t) :=by
    let I:=lensS J su; let g:= pitch J X d β V; have hh (z : Poll.Body (↥I)) : DifferentiableAt ℝ g z := by
       nth_rw 1 [← Pond.settled I z]; exact (blocks J X h hB V hp _).differentiableAt
    have hi:= Flux.across J X h hB V hp
    have hF:= integral_image_eq_integral_abs_det_fderiv_smul volume (s:=Set.univ) MeasurableSet.univ (fun x _=>
     (hh x).hasFDerivAt.hasFDerivWithinAt) hi.1.injOn p
    rw [Set.image_univ, Set.range_eq_univ.mpr hi.2,setIntegral_univ,setIntegral_univ] at hF
    refine hF.trans (integral_congr_ae (ae_of_all _ fun z=>?_)); have hh:= almanac J X h hB V hp (Pond.spill I z)
    rw [Pond.settled] at hh; change |(fderiv ℝ (pitch J X d β V) z).det| • _=_; rw [hh,abs_of_pos (jac_pos J X V hp ..)]
lemma bouquet (B:Finset (Tubular f su))(A:Matrix (↥B) (↥B) ℝ)(h:A.PosDef)(U:Poll.Body (↥B)→ EvenA c N): (∫ x,U x ∂ Poll.sweep A)=∫ z,lens₀ A z • U z :=by
    rw [magnifies _ h, integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x=> ENNReal.ofReal (lens₀ A x)) from ENNReal.measurable_ofReal.comp (bulbB (S:=fun _ : (Poll.Body (↥B))=> A) (fun i j=>measurable_const) (z:=id) measurable_id)) (ae_of_all _ fun x=> ENNReal.ofReal_lt_top)]; exact integral_congr_ae (ae_of_all _ fun z=> by dsimp only; rw [ENNReal.toReal_ofReal (Shield.fullFuel A z).le])
set_option maxHeartbeats 280000 in
lemma billS (h:Y.Famous)(he:Y.speaking)(V: Config su c)(u:I')(ht:X.x=s)(hk:X.width=o.K)(hX:X.relating.PosDef)(hd:Canary su d A)(hp:Drivable X d A V): let I:=edgesM S (Y.fullA u) (radiusB s)
    Y.lows (podium S su (Y.fullA u) (radiusB s)) u (vary X V) = ∫ x,(∫ z, arts Y I d u (X.wrapY x) V z ∂ X.dice) ∂ F.order su :=by
    intro I; rw [← chargedU]; let D:= lensS I su; let A':= circuit D X.relating; have hD:D=podium S su (Y.fullA u) (radiusB s):= chargedU ..
    unfold Fleet.lows; apply integral_congr_ae; filter_upwards with x; let Z:=X.wrapY x; let B:= (vary Z V); let M v:= cactus Y u B v; let p t:= lens₀ (circuit D B.relating) t • M (spill D t); let f' v:= arts Y I d u Z V v
    have hh:Drivable Z d A V :=⟨fun i=>hp.good i⟩
    have hv:Measurable f':=by
       let g (a:Air f su):= (x,a); have he:Measurable g:= measurable_const.prodMk measurable_id; change Measurable (playM Y I d u X V ∘ g)
       exact (nectar Y X (by assumption) ht hk V hd hp u I).comp he
    have hF:MeasurePreserving (swim D) X.dice (Poll.sweep A'):= Pond.orbit hX.posSemidef D
    have hs:∀ v z, swim D v=swim D z → f' v=f' z :=by
       intro v z h; unfold f' arts; rw [slab I Z V v z h d]
       change swim (lensS I su) v=swim (lensS I su) z at h; have ht':= congr_arg (pitch I Z d R.beta V) h; rw [pitch_alt,pitch_alt] at ht'
       exact congr_arg _ (transitS Y B (by assumption) ht _ _ _ (hD ▸ ht')) -- shadow
    change (∫ z,p z) = ∫ z,f' z ∂ X.dice
    have he:(∫ z,f' z ∂X.dice)=∫ v,f' (spill D v) ∂ Poll.sweep A':=by
        let q v:= f' (spill D v); change _=∫ x,q x ∂_; rw [← hF.map_eq, integral_map hF.measurable.aemeasurable ((show Measurable q from hv.comp (spill_m D)).aestronglyMeasurable)]; exact integral_congr_ae (ae_of_all _ fun i=> hs i _ (Pond.settled D _).symm)
    rw [he,rake Z I hd V hh H.laws.intake.positive p,bouquet _ A' (hX.submatrix Subtype.val_injective)]
    apply integral_congr_ae; filter_upwards with v
    let z:=spill D v; let g:=pitch I Z d R.beta V v; let r:=course Z d R.beta z V; let t':=lens₀ (circuit D B.relating) g
    change jacL I Z d R.beta V z • (t' • M (spill D g))=lens₀ A' v • (scalp I Z V R.beta d z • M r)
    rw [show M (spill D g)=M r from transitS Y B h ht _ _ _ (hD ▸ Pond.settled D g),← mul_smul _ t' (M r),← mul_smul (lens₀ A' v) _ (M r)]; apply congr_arg₂ _ _ rfl
    rw [Flux.scalp]
    rw [show swim (lensS I su) z=v from settled D v]; change _=_ * (_ * (t'/lens₀ A' v)); field_simp [(Shield.fullFuel A' v).ne'] <;> ring
end YM.ConnectedActivityE6.Blaze.Golden
