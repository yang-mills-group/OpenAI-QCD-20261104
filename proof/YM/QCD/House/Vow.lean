import YM.QCD.House.Parts

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
set_option quotPrecheck false
set_option maxHeartbeats 600000 in
lemma margG (T:Type*)[NormedAddCommGroup T][NormedSpace ℝ T][CompleteSpace T][MeasurableSpace T][BorelSpace T][SecondCountableTopology T]
 (P: Finset (Tubular f su))(A:Matrix (Tubular f su) (Tubular f su) ℝ) (X: Air f su→ T) (hm:Measurable X)(he : A.PosDef) (hp:∀ i j, swim P i=swim P j → X i=X j) :
 (∫ z:Body (↥P), lens₀ (circuit P A) z • X (spill P z))=∫ z,X z ∂ Poll.sweep A:=by
   let C:=circuit P A
   have hC:C.PosDef:=he.submatrix Subtype.val_injective
   let q x:= X (spill P x); let m:= Poll.sweep A
   have hf : (∫ z,X z ∂m)=∫ x,q x ∂arch P A:=by
       have hq:MeasurePreserving (swim P) m (arch P A):=Pond.orbit he.posSemidef P
       have hv: AEStronglyMeasurable q (m.map (swim P)):= (hm.comp (spill_m P)).aestronglyMeasurable
       rw [← hq.map_eq, integral_map hq.measurable.aemeasurable hv]
       exact integral_congr_ae (ae_of_all _ fun i=> hp i _ (Pond.settled P _).symm)
   change (∫ z:Body (↥P), lens₀ C z • q z)=∫ z,X z ∂m
   rw [hf,arch, magnifies _ hC, integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x=> ENNReal.ofReal (lens₀ C x)) from ENNReal.measurable_ofReal.comp (bulbB (S:=fun _ : (Body (↥P))=> C) (fun i j=>measurable_const) (z:=id) measurable_id)) (ae_of_all _ fun x=> ENNReal.ofReal_lt_top)]
   apply integral_congr_ae; filter_upwards with i; rw [ENNReal.toReal_ofReal (Shield.fullFuel C i).le]
-- edit Mat reference
set_option maxHeartbeats 500000 in
lemma rag (X:C' F)(s:I)(I': Finset (Tubular f su))(p:X.manifest) (hx:X.x=τ)(y :F.Slice su)(hV:Healthy (Pressure.temp τ) (Y.fullA s) X.V)(z):
 Y.regards I' s X y z= lens₀ (circuit I' X.relating) z • (Y.suitcase F).capacityP s (own s.toLeft) (X.wrapY y) (spill I' z):=by
       let V:= Y.suitcase F; let k:= own s.toLeft; let X':= X.wrapY y; let C:=circuit I' X.relating
       have hW:Room P S T X'.x:=hx.symm ▸ H.laws.data.room
       have hR i (hi:i∈s.toRight): Y.muscle i X' (spill I' z)=Y.coming i X' (spill I' z):=by unfold muscle coming riseP; rw [Vine.shine X' hW p R.beta]
       refine congr_arg (fun x:EvenA c N=> lens₀ C z • x) (congr_arg₂ (fun (r:ℝ) (u:EvenA c N)=> r • u) ((Polar.afterborn X' o.a R W Q.table (spill I' z) k hW p Q.buys s.toLeft ?Will)).symm (prod_congr rfl hR))
       case Will =>
        change Healthy (Pressure.temp X.x) (Matter.ground R T Q.halo (radiusB X.x) s.toLeft) _; rw [hx]; exact Finset.disjoint_of_subset_left (V.lesserP s) hV
lemma tippers (X:C' F)(s:I) (hx:X.x=τ)(hk:Y.Famous) (v u: Air f su) (hr: Pond.swim (podium S su (Y.fullA s) (radiusB τ)) v=Pond.swim (podium S su (Y.fullA s) (radiusB τ)) u):
    (Y.suitcase F).capacityP s (own s.toLeft) X v= (Y.suitcase F).capacityP s (own s.toLeft) X u:= by
        let W:= Y.fullA s; let V:= Y.suitcase F; have h1:Borough X X W v u (own s.toLeft) (own s.toLeft) R := ⟨Village.refl ..,fun i hi=> (Pond.observe _).1 hr i (by change i∈podium S su W (radiusB X.x) at hi; rw [hx] at hi; exact hi), fun _ _=> Iff.rfl⟩
        exact V.habitat (own s.toLeft) (own s.toLeft) s (Y.forwarded _ hk) X X v u hx h1
lemma flowerB {Y':Type*} [MeasurableSpace Y'] (T: Type*) [NormedAddCommGroup T][NormedSpace ℝ T][CompleteSpace T][MeasurableSpace T][BorelSpace T][SecondCountableTopology T]
 (P: Finset (Tubular f su))(M: Matrix (Tubular f su) (Tubular f su) ℝ)(m:Measure Y')[IsFiniteMeasure m](Q: Y' → Body (↥P)→T)(X: Y' × Air f su→T) (h:Envelope X) (ht: M.PosDef) (hp:∀ y i,Q y i= lens₀ (circuit P M) i • X (y,spill P i))(he:∀ y i j,Pond.swim P i=Pond.swim P j→X (y,i)=X (y,j)):
 (∫ y,(∫ z,Q y z) ∂m)=∫ z,X z ∂ m.prod (Poll.sweep M):=by
    have hm: Integrable X (m.prod (Poll.sweep M)):= envPlot h _
    rw [integral_prod _ hm]; apply integral_congr_ae; filter_upwards with y; simp_rw [hp]; exact margG T P M _ (h.meas.comp (measurable_const.prodMk measurable_id)) ht (he y)
set_option maxHeartbeats 400000 in
lemma germ_e (X:C' F)(s:I)(hx:X.x=τ)(hk:X.width=o.K) (p:X.manifest)(hV:Healthy (Pressure.temp τ) (Y.fullA s) X.V)(h:Y.Famous) :
   Y.lows (podium S su (Y.fullA s) (radiusB τ)) s X=call X ((Y.suitcase F).capacityP s (own s.toLeft)):=by
    let V:=Y.suitcase F; let k:=own s.toLeft; let I':=podium S su (Y.fullA s) (radiusB τ)
    have ht := V.ripeP k s (Y.forwarded _ h) X hx hk p
    exact flowerB _ I' X.relating (F.order su) (fun y z=> Y.regards I' s X y z) _ ht (H.laws.data.localP F X hx hk p).sails.fullC (fun y z=>rag Y X s I' p hx y hV z) (fun y i j=> tippers Y (X.wrapY y) s hx h i j)

def bandL (s:I)(X:C' F):EvenA c N:= if Ac.Spark (Y.suitcase F).gP s∧(Y.suitcase F).born s then choiceS fun i:S.Choices=> Y.lows (podium S su (Y.fullA s) (radiusB τ)) s ((preps X (roster s.toLeft)).taggedL i) else 0
set_option maxHeartbeats 850000 in
lemma crownL (X:C' F)(s:I)(hx:X.x=τ)(hk:X.width=o.K) (h:Y.Famous)(hp:(roster s.toLeft).flags=∅) : (Y.suitcase F).shootsP X s=masked (Pressure.temp τ) (Y.fullA s) (fun V=>Y.bandL s (vary X V)) X.V:=by
   unfold Pipe.shootsP bandL; by_cases he:Healthy (Pressure.temp τ) (Y.fullA s) X.V
   swap; · rw [masked_ne _ _ _ _ he,if_neg]; intro ht; apply he; apply Finset.disjoint_iff_inter_eq_empty.mpr; rw [inter_comm]; have hx':=ht.2.2.trans hp; rw [hx] at hx'; exact hx'
   rw [masked_eq _ _ _ _ he, show RG.flags (Pressure.temp X.x) X.V ∩(Y.suitcase F).full s=(roster s.toLeft).flags from ?_]
   rotate_left
   · rw [hp, hx, inter_comm]; exact Finset.disjoint_iff_inter_eq_empty.mp he
   by_cases hv: Ac.Spark (Y.suitcase F).gP s∧(Y.suitcase F).born s
   swap; · simp [hv]
   rw [if_pos ⟨hv.1,hv.2,rfl⟩,if_pos hv]; unfold draws; apply congr_arg; funext i
   let U:=(planted X s.toLeft).taggedL i; let Z:=(preps X (roster s.toLeft)).taggedL i; rw [← show Y.lows _ _ U=_ from germ_e Y U s hx hk (planted_valid ..) he h]
   refine readL Y U Z s h hx ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
   intro j hj; unfold U Z; simp only [taggedL,planted,preps,Stores.place,hp,hx,union_empty,mem_union] -- edit
   have ht:j∉ RG.flags (Pressure.temp τ) X.V:=Finset.disjoint_left.mp he hj; tauto
lemma capsuleL (X:C' F)(s:I)(hx:X.x=τ)(hk:X.width=o.K)(h:Y.Famous)(hp:Y.speaking) : LocalOn (Y.fullA s) (fun V=>Y.bandL s (vary X V)) ∧ Measurable (fun V=>Y.bandL s (vary X V)):=by
   unfold bandL; split
   · refine ⟨fun V U he=> congr_arg choiceS (funext fun i=> ?_), measurable_const.smul (Finset.measurable_fun_sum _ fun i _=> ?_)⟩
     · exact readL Y ((preps (vary X V) (roster s.toLeft)).taggedL i) ((preps (vary X U) (roster s.toLeft)).taggedL i) s h hx ⟨rfl,rfl,rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,he⟩
     exact Y.lensRead ((preps X (roster s.toLeft)).taggedL i) s _ hp hx hk
   exact ⟨fun _ _ _=> rfl,measurable_const⟩
-- unsymmetric envelope. by Forest and full V; exact. next smooth then sym.
def brisk (s:I)(χ:Chi)(V:Grid c): EvenA c N:= choiceS (fun i:Reserve S=> Y.bandL s (V' χ o.K V (allot i)))
lemma brass (s:I)(χ:Chi)(h:Y.Famous)(hp:Y.speaking):LocalOn (Y.fullA s) (Y.brisk s χ) ∧Measurable (Y.brisk s χ):=by
   have ht i := capsuleL Y (V' χ o.K (1:Grid c) (allot i)) s rfl rfl h hp
   exact ⟨fun V U hv=> congr_arg choiceS (funext fun i=> (ht i).1 V U hv), measurable_const.smul (Finset.measurable_fun_sum _ fun i _=> (ht i).2)⟩
lemma wholeC (s:I)(χ:Chi)(h:Y.Famous)(hp:(roster s.toLeft).flags=∅) : Y.vF s χ= masked (Pressure.temp τ) (Y.fullA s) (Y.brisk s χ):=by
   funext U
   let X i:= V' χ o.K U (allot i)
   unfold vF
   have hh i:=crownL Y (X i) s rfl rfl h hp
   by_cases hx:Healthy (Pressure.temp τ) (Y.fullA s) U
   · rw [masked_eq _ _ _ _ hx]; exact congr_arg choiceS <| funext fun i=> (hh i).trans (masked_eq _ _ _ U hx)
   rw [masked_ne _ _ _ _ hx]; have hg i:(Y.suitcase (allot i)).shootsP (X i) s=0:= (hh i).trans (masked_ne _ _ _ U hx)
   change choiceS (fun i=> (Y.suitcase ..).shootsP (X i) s)=0; simp_rw [hg]; simp only [choiceS,sum_const_zero,smul_zero]
end YM.QCD.Loom.Fleet
