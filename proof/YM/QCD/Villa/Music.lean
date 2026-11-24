import YM.QCD.Villa.Coin
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Glints

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
open Art
open Art Hues
-- since K chir/flavor physical conventions all Real-linear
structure sings (Z:Site c→ su.El)(P:EvenA c N→+* EvenA c N) :Prop where
 cont : Continuous P
 verse i x y: P (Y.works i (gauge (constantGauge Z S.ratio) x) (gauge Z y)) = Y.works i x y
lemma vocals {M M' :Type*}[MeasurableSpace M][MeasurableSpace M'] (Q:EvenA c N →+*EvenA c N)(hP:Continuous Q){m:Measure M}{m':Measure M'}{p:M→M'} (H:MeasurePreserving p m m'){u:M→ EvenA c N}{v:M'→EvenA c N}(h:Measurable v)(he:Integrable u m)(ht:Integrable v m')(hp:∀ x,Q (v (p x))=u x): Q (∫ x,v x ∂m')=∫ x,u x ∂m:=by
   let f:= Q.toAddMonoidHom.toRealLinearMap hP; apply concrete; intro l; have hq : l (Q (∫ x,v x ∂m'))=∫ x,(l.comp f) (v x) ∂m' := ((l.comp f).integral_comp_comm ht).symm
   rw [hq,← ContinuousLinearMap.integral_comp_comm _ he]; let g x:=(l.comp f) (v x); rw [← Pond.reception H g ((l.comp f).measurable.comp h)]
   exact integral_congr_ae (ae_of_all _ fun x=>congr_arg l (hp x))
lemma eSM (K:EvenA c N →+* EvenA c N)(h:Continuous K)(x:ℝ)(y:EvenA c N):K (x • y)= x • K y := map_real_smul K h x y
set_option maxHeartbeats 1000000 in
lemma riff {Z:Site c→su.El}{K:EvenA c N →+*EvenA c N} (Q:Y.sings Z K)(u:I)(A:C' F)(k: Finset ℕ) (hx:A.x=τ)(ht:A.width=o.K)(hs:A.manifest)(j:Air f su): K ((Y.suitcase F).capacityP u k (Hues.sluice A Z) (weep A Z j))=(Y.suitcase F).capacityP u k A j:=by
    have hf:ShellAccess S su A.x W A.width o.γ:= by rw [hx,ht]; exact H.laws.data.access
    unfold Pipe.capacityP; rw [eSM K Q.cont]; apply congr_arg₂ (· • ·)
    · exact prod_congr rfl fun i _=> H.scours A hx ht hs k Z j i
    unfold Pipe.averageP; rw [map_prod]; refine Finset.prod_congr rfl fun i _=>?_
    change K (Y.coming i (Hues.sluice A Z) (weep A Z j))= _; unfold coming riseP; rw [eSM K Q.cont,Hues.fullA _ _ H.laws.intake.ready hf,banks]
    exact congr_arg₂ (· • ·) (Hues.mandate A Z (2*o.a) _ (A.plaza (Y.window i))) (Q.verse i _ A.V)
lemma earns {Z:Site c→su.El}{K:EvenA c N→+*EvenA c N} (Q:Y.sings Z K)(s:I)(h:Y.Famous)(X:C' F)(hp:X.x=τ)(he:X.width=o.K) : K ((Y.suitcase F).shootsP (X.rinse Z) s)=(Y.suitcase F).shootsP X s:=by
   let U:=Y.suitcase F; let A:= Matter.planted X s.toLeft; let k:=Matter.own s.toLeft
   let R':=U.capacityP s k
   unfold Pipe.shootsP; rw [show (X.rinse Z).x=X.x from rfl,show (X.rinse Z).V=gauge Z X.V from rfl,gauge_flags]; split
   swap; · exact map_zero _
   next hk=>
   have hv : Matter.planted (X.rinse Z) s.toLeft = A.rinse Z:= by unfold A Matter.planted rinse preps; simp only [gauge_flags]
   rw [hv]; unfold draws choiceS; rw [eSM K Q.cont,map_sum]; apply congr_arg; refine sum_congr rfl fun i _=>?_
   let Z':=A.taggedL i; let W':= (A.rinse Z).taggedL i; let Y':= Hues.sluice Z' Z; have hz:=H.laws.data
   have hn: Z'.manifest:= Matter.planted_valid X s.toLeft; have hM:Y'.manifest:=Cash.wind Z' Z hn
   let Q' (t:F.Slice su×Air f su) := R' (Y'.wrapY t.1) t.2; have ht:= U.ripeP k s (Y.forwarded _ h) Y' hp he hM; have ht' := U.ripeP k s (Y.forwarded _ h) Z' hp he hn
   have hv : MeasurePreserving (fun v:F.Slice su×Air f su=> (Hues.pairs Z' Z v.1, weep Z' Z v.2)) ((F.order su).prod Z'.dice) ((F.order su).prod Y'.dice) := (Hues.drinking Z' Z).prod (Hues.speeds Z' Z H.laws.intake.ready (hz.localP F Z' hp he hn).sails.fullC (hz.localP F Y' hp he hM).sails.fullC)
   exact vocals K Q.cont hv ht.1 (envPlot ht' _) (envPlot ht _) fun p=>riff Y Q s (Z'.wrapY p.1) k hp he hn p.2
lemma factor {Z:Site c→su.El}{K:EvenA c N→+*EvenA c N}(Q:Y.sings Z K)(s:I)(h:Y.Famous)(χ:Chi)(V:Grid c): K (Y.vF s χ (gauge Z V))=Y.vF s χ V:=by
    unfold vF choiceS; rw [eSM K Q.cont,map_sum]; apply congr_arg; refine sum_congr rfl fun i _=>?_ ; exact earns Y Q s h (V' χ o.K V (allot i)) rfl rfl
end YM.QCD.Loom.Fleet
