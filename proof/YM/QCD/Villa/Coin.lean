import YM.QCD.Villa.Brio

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
def vF (s:I)(χ:Chi) (V: Grid c): EvenA c N:= choiceS (fun i:Reserve S=> let X:=V' χ o.K V (allot i);(Y.suitcase (allot i)).shootsP X s)
def okClump (s:Finset I):Prop:=((Y.suitcase (Classical.choice (Tree.select S.ratio S.patch.odd_side))).legal s)
def emergingF (s: Finset I) (χ: Chi) (V:Grid c):EvenA c N:=if Y.okClump s ∧ RG.flags (Pressure.temp τ) V=s.biUnion (fun i=>(roster i.toLeft).flags) then ∏ i∈s,Y.vF i χ V else 0
lemma ambitS (s:I)(χ:Chi)(h:Y.Famous):UsesFinal (Pressure.temp τ) (Y.fullA s) (Y.vF s χ):=by intro U V hU hV; refine congr_arg choiceS (funext fun i=>spacial Y s h (V' χ o.K U (allot i)) (V' χ o.K V (allot i)) rfl rfl rfl rfl rfl hU hV (fun _ _=>rfl))
lemma readableB (s:I)(χ:Chi)(h:Y.Famous)(hp:Y.speaking):Measurable (vF Y s χ):=by unfold vF choiceS; refine measurable_const.smul (Finset.measurable_fun_sum _ fun i _=>?_); exact recordB Y (X:=V' χ o.K 1 (allot i)) s h hp rfl rfl
lemma fnT (M:Type*) [NormedCommRing M][NormedAlgebra ℝ M][Fintype ι][Nonempty ι](x:M):choiceS (fun _:ι=>x)=x:=by unfold choiceS; simp [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
set_option maxHeartbeats 850000 in
lemma ensemble (V:Grid c)(χ:Chi)(h:Y.Famous)(s:Finset I):Y.emergingF s χ V= choiceS (fun i:Reserve S=> (Y.suitcase (allot i)).drawP (V' χ o.K V (allot i)) s):=by
   letI : Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
   unfold emergingF; let p i:=(Y.suitcase (allot i)); let X i:= V' χ o.K V (allot i); let f i:= (p i).drawP (X i) s
   split
   next hs=>
     have hv i:f i=∏ j:↥s,(p i).shootsP (X i) j.val:= by unfold f Pipe.drawP; rw [if_pos (show (p i).legal s ∧ RG.flags (Pressure.temp (X i).x) (X i).V = s.biUnion (fun j=> (roster j.toLeft).flags) from hs),← prod_coe_sort s]
     rw [← prod_coe_sort s]
     change _ = choiceS f
     simp_rw [funext hv]
     symm
     let u (j:↥s)(i:Reserve S):= (p i).shootsP (X i) j.val
     -- over Vote.S vector
     refine Beam.fairT («I»:=Site c) (A:=Tree.Forest S.ratio) (Y:=↥s) (inferInstanceAs (Fintype (Reserve S))) u (Y.fullA ∘ fun j:↥s=>j.val) ?_ ?_
     · intro i _ j _ hn; exact hs.1.2 i.2 j.2 (fun h=> hn (Subtype.ext h))
     intro j r v hh; apply spacial Y j.val h (X r) (X v) rfl rfl rfl rfl rfl (fun _ _ _=>rfl) rfl
     intro i hi; change (r (S.ratio.parent i)).up i=(v (S.ratio.parent i)).up i; rw [hh _ hi]
   next hs=>
     have hv i:f i=0 := if_neg hs
     change 0=choiceS f; rw [funext hv]; exact (fnT (ι:=Reserve S) (EvenA c N) 0).symm
lemma hS {A B:Type*}[Fintype B](M:Type*) [NormedAddCommGroup M][NormedSpace ℝ M](Y:A→B→M)(p:B→M)(h:∀ b,HasSum (fun i=>Y i b) (p b)): HasSum (fun i=>(Fintype.card B:ℝ)⁻¹ •∑ b:B,Y i b) ((Fintype.card B:ℝ)⁻¹ •∑ b:B,p b):=((hasSum_sum (s:=univ) (fun i _=>h i)).const_smul _)
lemma pushF [Fintype ι](X:C' F)(h:Y.Famous)(he:X.x=τ)(ht: GaugeInvariant R.exponent):
   let f:=(Y.suitcase F).missP X.V
   HasSum (fun s=> Matter.overhead X R Q.table • Y.emergingF s X.χ X.V) (S.push R.beta f X.V) :=by
    intro f; letI : Nonempty (Tree.Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    let V i := V' X.χ o.K X.V (allot i); let Z:= Matter.overhead X R Q.table
    let W s i:= (Y.suitcase (allot i)).drawP (V i) s
    have hp i: Matter.overhead (V i) R Q.table=Z:=TreeColor.overhead_eq (V i) X he.symm H.laws.intake.ready rfl Q.table R
    have hZ s: Z • Y.emergingF s X.χ X.V=choiceS fun i:Reserve S=> Z • W s i:=by
       rw [ensemble Y X.V X.χ h s,choiceS,choiceS,smul_comm,Finset.smul_sum]
    have hx i:HasSum (fun s=>Z • W s i) (S.push R.beta f X.V):=by rw [← hp i] ; exact (Y.suitcase (allot i)).filledP (V i) (Y.forwarded _ h) rfl rfl ht
    change HasSum (fun s=> Z • _) _
    simp_rw [hZ]
    nth_rw 1 [← fnT (ι:=Reserve S) _ (S.push R.beta f X.V)]; exact hS _ _ _ hx
end YM.QCD.Loom.Fleet
