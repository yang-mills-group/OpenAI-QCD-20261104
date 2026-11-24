import YM.QCD.Villa.Glow
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pattern

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
local notation "V'"=> prism T τ
open Art Blaze Polar Shield Frond
-- Extension as equality even on masked boundary. Whole reads.
def muscle (i:ι)(X:C' F)(z:Air f su) : EvenA c N:=
 let p:=Vine.worldZ X R.beta z
 X.enforce (2*o.a) p (X.plaza (Y.window i)) • Y.works i (X.input p) X.V
lemma older (i:ι)(X:C' F)(z:Air f su): Y.muscle i X z=Y.coming i X (X.reform R.beta (Vine.worldZ X R.beta z)):=by
   unfold muscle coming riseP; rw [X.oldysis H.laws.intake.positive]
def regards (p: Finset (Tubular f su))(s:I)(X:C' F)(t:F.Slice su)(z:Body (↥p)): EvenA c N:=let k:=spill p z; let U:= X.wrapY t
 lens₀ (circuit p X.relating) z • (Polar.floating U o.a R W Q.table k (own s.toLeft) Q.halo s.toLeft • ∏ i∈s.toRight,Y.muscle i U k)
def lows (p: Finset (Tubular f su))(s:I)(X:C' F): EvenA c N:=∫ t,(∫ z,Y.regards p s X t z) ∂ F.order su
lemma readL (X Z:C' F)(u:I)(h:Y.Famous)(hx:X.x=τ)(hp:Village X Z (Y.fullA u)) : Y.lows (podium S su (Y.fullA u) (radiusB τ)) u X=Y.lows (podium S su (Y.fullA u) (radiusB τ)) u Z:=by
   let p:= podium S su (Y.fullA u) (radiusB τ)
   have hB : Room P S T X.x:=hx.symm ▸ H.laws.data.room
   have hP:p=podium S su (Y.fullA u) X.B:=by unfold p Coat.B; rw [hx]
   have hV:circuit p X.relating=circuit p Z.relating:=by ext i j; exact hp.same_cov hB j.val (hP ▸ j.2) i.val
   unfold lows; apply integral_congr_ae; filter_upwards with t
   apply integral_congr_ae; filter_upwards with z
   let k:=own u.toLeft; let A:= X.wrapY t; let B:= Z.wrapY t; let U:= spill p z
   have hh: Village A B (Y.fullA u):= hp.wrap _ _ (fun _ _=>rfl)
   have hg: Borough A B (Y.fullA u) U U k k R:=⟨hh,fun _ _=>rfl,fun _ _=> Iff.rfl⟩
   have hf:(Matter.ground R T Q.halo X.B u.toLeft)⊆ Y.fullA u:=by unfold Coat.B; rw [hx]; exact (Y.suitcase F).lesserP u
   have hw: ∀ i∈u.toRight,Y.muscle i A U=Y.muscle i B U :=by
      intro i hi; rw [older,older]; have h' := hg.rooms hB R.beta; apply buds Y i (h:=h) A B _ _ hx
      · have ht:= (Y.suitcase F).leP u hi; change Y.ground i ⊆ Y.fullA u at ht; exact ⟨hh.weather,hh.width,hh.chi,fun _ h=> hh.places _ (ht h),fun _ h=> hh.frames _ (ht h),fun _ h=> hh.site _ (ht h),fun _ h=> hh.bond _ (ht h),agrees_mono hh.actual ht⟩
      exact (Pond.observe _).2 fun j hj=> h'.airs j (mem_filter.mpr ⟨mem_univ _,fun x hx=>(Y.suitcase F).leP u hi ((mem_filter.mp hj).2 _ hx)⟩)
   unfold regards; dsimp only; rw [show circuit p X.relating=_ from hV]; apply congr_arg; refine congr_arg₂ (· • ·) (hg.flops hB Q.buys (hx.symm ▸ H.laws.intake) _ _ _ hf) (prod_congr rfl hw)
lemma lensRead (X:C' F)(u:I)(p:Finset (Tubular f su))(hp:Y.speaking)(he:X.x=τ)(hk:X.width=o.K) : Measurable fun V=> Y.lows p u (vary X V):=by
    let A:= (Grid c × F.Slice su) × Body (↥p)
    let U (i:A):=i.1.1; let Y₀ (i:A):=i.1.2; let Z (i:A):=spill p i.2
    have hU: Measurable U:=measurable_fst.comp measurable_fst; have hY:Measurable Y₀:=measurable_snd.comp measurable_fst; have hZ: Measurable Z:= (spill_m p).comp measurable_snd
    let W' i:= Art.drive X (U i) (Y₀ i)
    have hf:= H.laws.data
    have hv:ShellAccess S su X.x W X.width o.γ:=by rw [he,hk]; exact hf.access
    have hh := c_measured X.shutter (A:=fun i=> (vary X (U i)).plate) (fun i j=> (Art.borel_plate X H.laws.intake.ready i j).comp hU)
    have hp' j: Measurable fun i=> Y.muscle j (W' i) (Z i):=by
      let z i:=Vine.worldZ (W' i) R.beta (Z i); have ht:Measurable z:=(compassBro H.laws.intake.ready hU X hY hv R.beta).2.2 Z hZ
      exact ((X.enforce_b _ (X.plaza (Y.window j))).comp ht).smul ((hp j).comp ((Art.entering X hU hY ht).prodMk hU))
    have he':Measurable fun i:A=> Y.regards p u (vary X (U i)) (Y₀ i) i.2:= (Shield.bulbB (S:=fun i=> Pond.circuit p (vary X (U i)).relating) (fun i j=> hh.1 i.val j.val) measurable_snd).smul ((Shield.collectionB X hv (he.symm ▸ H.laws.intake) Q.table_exists hU hY hZ (own u.toLeft) o.a Q.halo u.toLeft).smul (Finset.measurable_fun_prod _ (fun i _=>hp' i)))
    exact ((he'.stronglyMeasurable.integral_prod_right' (ν:=volume)).integral_prod_right' (ν:=F.order su)).measurable
end YM.QCD.Loom.Fleet
