import YM.QCD.Loom.Volt
import YM.QCD.Loom.Issue
/-! # Full integration dictionary to output at actual densities. Includes all spectator effects. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {η p h z a a' t v V u u' q:ℝ} {K J:Type}[Countable K][Countable J]
variable (L:Flight j k)(d:f.val=c.val*L.L.val)(O:KernelChoices)
variable {T : Tube su (Flight.visit L O d)} {W' :ℕ→Atom su 2} {P':Plan k}
variable {X : St f}
local notation "S"=> Flight.visit L O d
local notation "PI"=> trimP T R δ β b
variable (p:Rise f N J K)(H:Cash W τ μ L.L Q o C T (trimP T R δ β b)) (G:Sun L c f d η h z a a' m X) (V':Swathe L d X W' P' h η a u v i)
local notation "Z"=> G.equip N (radiusB τ)
local notation "U"=> roof (Z) p 30 (radiusB τ)
variable (Γ: Land c (Site c) (Site c)){Y: Pays c (Site c) (Site c)}
def tableau : Fleet H (Wound (U) ⊕ Varn f c⊕Gaze c) N:= united (deckHue H (Z) p (U)) (united (VarnC H V' N) (sailP H Γ N))
-- useful formula Unite instead nesting tag body. v selections. prove.
lemma weaveProd (A:Finset (Wound U)) (F:Tree.Forest (S).ratio)(U₁:Grid f)(W₀:Grid c):
    let Y:=united (VarnC H V' N) (sailP H Γ N);(∑ s:Finset (Varn f c⊕Gaze c),∏ i∈s,Y.works i U₁ W₀)= (∑ s:Finset (Varn f c),∏ i∈s,broke V' N (radiusB τ) i U₁) * (∑ s:Finset (Gaze c),∏ i∈s,(sailP H Γ N).works i U₁ W₀):=by
    intro Y; let M:= Varn f c; let P':Finset M×Finset (Gaze c)≃ Finset (M⊕Gaze c):={ toFun:=fun p=>p.1.disjSum p.2, invFun:=fun p=>(p.toLeft,p.toRight), left_inv p:=Prod.ext (toLeft_disjSum ..) (toRight_disjSum ..),right_inv p:=by ext i; cases i<;> simp }; rw [← Equiv.sum_comp P', Fintype.sum_prod_type,Finset.sum_mul]; refine sum_congr rfl fun p _=>?_ ; rw [Finset.mul_sum]; refine sum_congr rfl fun i _=>?_ ; change (∏ j∈p.disjSum i,Y.works j U₁ W₀)=_; rw [prod_disjSum]; rfl
lemma gamma (D E:Sheet c)(F:ℕ): gauss (Lat.copies F D)=Cove.light _ (NormedSpace.exp (paleF F (D-E))) * gauss (Lat.copies F E):=by
    rw [light_exp,serviceP,← gauss,← gauss_add,show Lat.copies F (D - E)= Lat.copies F D-Lat.copies F E from Matrix.blockDiagonal_sub .., sub_add_cancel]

lemma hymn (F:Tree.Forest (S).ratio){θ:ℝ}(h': Pack id id θ u' l (wood P' 0 L.land) q Γ Y)(hz:Cove.Count Z p U)(hv:p.Wave R.threshold)(hd:0<δ)(U₁:Grid f)(W₀:Grid c)(hh:Placid p R.threshold U₁):
    let Y₁:= (S)
    let M':= Y₁.density β U₁ W₀
    let f':= (Real.exp ((PI).exponent U₁):ℝ) • ( (↑(Real.exp (- Extra.Iteration.action W' U₁)):ℂ)^N • (sheath 1 (ater L d U₁) (gauss (starPerf L d X N U₁)*p.bluff R.threshold U₁)))
    let U':= tableau L d O p H G V' Γ
    f'= (X 1).det^N • (Cove.light _ ((U'.suitcase F).missP W₀ U₁) * gauss (Lat.copies N (wood P' 0 L.land W₀))) :=by
   intro S' T1 X₀ U'
   unfold X₀; rw [Port.f_total V' p U₁ G (radiusB τ) U hz hv hh]
   let Q':= deckHue H (Z) p (U); let A₁:= VarnC H V' N; let A₂:= sailP H Γ N; let A₃:=united A₁ A₂
   have he: ∀ i j, A₃.compat i j:=by rintro (i|i) (j|j)<;> exact trivial
   have hf:∀ i, A₃.limit i=∅:=by rintro (a|b) <;> rfl
   have hk := soul (F:=F) H _ _ U W₀ U₁ hd hz hv hh
   have hr:= combining F Q' A₃ he hf U₁ W₀ hk.summable; unfold U'; rw [show ((tableau L d O p H G V' Γ).suitcase F).missP W₀ U₁= _ from hr];
   have hk := hk.tsum_eq; change ((Q'.suitcase F).missP W₀ U₁=_) at hk; rw [hk]; rw [show (∑ i,∏ x∈i,A₃.works x U₁ W₀)= _ from weaveProd L d O p H G V' Γ ∅ F U₁ W₀,budgetJ h' U₁ W₀ H]
   rw [gamma (c:=c) _ (wood P' 0 L.land W₀),smul_comm]; apply congr_arg
   let Ψ:=Cove.light (Keys c N); have HH (u:EvenA c N)(t:ℝ): Ψ (t • u)= t • Ψ u:= map_smul (Ψ.toLinearMap.restrictScalars ℝ) t u
   simp only [map_mul]; rw [show ∀ t:ℝ, ∀ u:EvenA c N,Cove.light (Keys c N) (t • u)=t • Cove.light (Keys c N) u from fun t u=>HH u t]; simp_rw [Algebra.smul_mul_assoc,mul_assoc]; rfl
def Emitter (T:Tube su (S)) (δ β b:ℝ)(R:BudgetPoint)(W':ℕ→Atom su 2)(X:St f)(U₁:Grid f) := Real.exp ((trimP T R δ β b).exponent U₁) • ((↑(Real.exp (-Extra.Iteration.action W' U₁)):ℂ)^N • Kit.sheath 1 (ater L d U₁) (gauss (starPerf L d X N U₁)*p.bluff R.threshold U₁)) -- W' implicit yes?
def Y'' (A: ModeE c N)(v:ℂ): EvenA c N →L[ℝ] ModeE c N := ContinuousLinearMap.restrictScalars ℝ (v • (ContinuousLinearMap.comp ((ContinuousLinearMap.mul ℂ (Alg (Keys c N))).flip A) (LinearMap.toContinuousLinearMap (Cove.light (Keys c N)).toLinearMap)))
lemma appliesY (v:ℂ)(K:ModeE c N) (i:EvenA c N): Y'' K v i=v • (Cove.light _ i*K) := rfl
lemma crop_generic {ι:Type}[Countable ι] (F:Tree.Forest (S).ratio)(P₀ :Pipe H F (EvenA c N) ι)(H₁:P₀.Viable)(X₁:Coat T F)(ht:X₁.x=τ)(hk:X₁.width=o.K)(C:ModeE c N)(v:ℂ)(hh:GaugeInvariant (PI).exponent)(hg:P₀.solves X₁.V)(hc:Summable (P₀.heldP X₁)):HasSum (fun i=> v • (Cove.light _ (Matter.overhead X₁ (PI) Q.table • P₀.drawP X₁ i)*C)) ((S).push β (Y'' C v ∘ P₀.missP X₁.V) X₁.V):=by
   let Uv:= P₀.missP X₁.V
   have hK := StepData.isKernel _ (funds_branch H.laws.data.funds.funds) β
   have hm : Integrable Uv (prior su f):= P₀.intC X₁ H₁ (P₀.canopyH X₁.V hg)
   have hg := P₀.allG X₁ H₁ ht hk hh hg hc
   have hL: (S).push β (Y'' C v ∘ Uv) X₁.V= Y'' C v ((S).push β Uv X₁.V):=by
      unfold StepData.push; rw [← (Y'' C v).integral_comp_comm (StepData.push_slice hK X₁.V Uv hm)]; simp_rw [map_smul]; rfl
   rw [show (S).push _ _ _= _ from hL]; simp_rw [← appliesY]; have hh: (PI).beta=β:=rfl; rw [hh] at hg; exact (Y'' C v).hasSum hg
set_option maxHeartbeats 1000000 in
lemma crop (F:Tree.Forest (S).ratio)(H₁:(tableau L d O p H G V' Γ).Famous) (X₁:Coat T F)(ht:X₁.x=τ)(hk:X₁.width=o.K){θ:ℝ}(h': Run.Pack id id θ u' l (wood P' 0 L.land) q Γ Y)(hz:Cove.Count Z p U)(hv:p.Wave R.threshold)(hd:0<δ)(hh:GaugeInvariant (PI).exponent)(hG:((tableau L d O p H G V' Γ).suitcase F).solves X₁.V)(hp:∀ i,Placid p R.threshold i)(hc:Summable (((tableau L d O p H G V' Γ).suitcase F).heldP X₁)):
   let P:=((tableau L d O p H G V' Γ).suitcase F); let Q':=X₁.V
   HasSum (fun i=> (X 1).det^N • (Cove.light _ (Matter.overhead X₁ (PI) Q.table • P.drawP X₁ i) * gauss (Lat.copies N (wood P' 0 L.land Q')))) ((S).push β (Emitter (T:=T) (δ:=δ) (β:=β) (b:=b) (R:=R) (W':=W') (X:=X) L d O p) Q'):=by
   intro P₀ V
   let Cw:= gauss (Lat.copies N (wood P' 0 L.land V))
   have he:= hymn L d O p H G V' Γ F h' hz hv hd
   have ht' := crop_generic L d O H F P₀ (Fleet.forwarded F _ H₁) X₁ ht hk Cw ((X 1).det^N) hh hG hc
   have hv : Emitter L d O p T δ β b R W' X = ((Y'' Cw ((X 1).det^N)) ∘ P₀.missP X₁.V):=by
       funext i; simp only [Function.comp_apply,appliesY]; exact he i V (hp i)
   rw [hv]; exact ht'
end YM.QCD.Loom
