import YM.Mural.Zodiac
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet.Palette
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Grass
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι I:Type}{N M:ℕ}
open Art Hues
open MassiveQCD.PaletteT
local notation "C'"=>Coat T
variable [Fintype I]
local notation "FI"=>Option I
local notation "I'"=> Pipe.Clump S ι
variable (Y:Fleet H ι N) (Γ:Option I→ ι→Grid f→ Grid c→EvenA c M)(T0: Site c→ su.El)
local notation "P'"=> EvenA c M
variable {Wc:Submodule ℂ (Option I→ EvenA c M)}{κ:Delta I}{g:EvenA c M→ₐ[ℂ]EvenA c M}
variable (h:Kit Y Γ T0 Wc κ g)
local notation "U" j'=> align Y (Γ j')
include h
open GasP Ursell Graph
lemma turf (χ:Chi)(V:Grid c)(u:I') : Binds κ g (fun i=> (U i).vF u χ (gauge T0 V)) (fun i=>(U i).vF u χ V) ∧ (fun i=> (U i).vF u χ V) ∈ Wc:=by
   unfold vF choiceS; let f(k:Reserve S)(i):= ((U i).suitcase (allot k)).shootsP (prism T τ χ o.K V (allot k)) u; let p(k:Reserve S)(i):=((U i).suitcase (allot k)).shootsP (prism T τ χ o.K (gauge T0 V) (allot k)) u
   have hp(k:Reserve S) : Binds κ g (p k) (f k):= blasts Y Γ T0 h (prism T τ χ o.K V (allot k)) u rfl rfl
   refine ⟨?_,?_⟩
   · simp_rw [← Complex.coe_smul ((Fintype.card (Reserve S):ℝ)⁻¹)]; exact binds_pin κ g 0 _ _ (binds_sum κ g _ p f (fun i _=>hp _)) _
   exact (Wc.restrictScalars ℝ).smul_mem (((Fintype.card (Reserve S):ℝ))⁻¹) (show (fun i=>∑ j:Reserve S, f j i)∈Wc from shines Wc f _ fun j _=> aspirates Y Γ T0 h _ _ rfl rfl)
lemma atTerrace (χ:Chi)(V:Grid c)(u:Clusters Y.Bright):
    Binds κ g (fun i=> (U i).honest χ (gauge T0 V) u) (fun i=>(U i).honest χ V u)∧(fun i=>(U i).honest χ V u)∈Wc:=by
    simp_rw [show ∀ (i:Option I) (v:Grid c), (U i).honest χ v u = termP (blocked Y.lightF) ((U i).dawnV χ v) u from fun i v=>phoenix _ χ _ (h.earns _) u]; unfold termP
    let f j i:= (U i).dawnV χ (gauge T0 V) (u.2 j); let p j i:= (U i).dawnV χ V (u.2 j);
    have hz(j): Binds κ g (f j) (p j)∧ p j∈Wc:= turf Y Γ T0 h χ V (u.2 j).val
    let y:=fun (i:FI)=>∏ j,p j i; let s:= ((u.fst+1).factorial:ℝ)⁻¹; let r:= (coefficient (blocked Y.lightF) u.2)
    have hx:y∈Wc:= gatheredX Wc p univ (fun i _=> (hz i).2) h.origin (fun i hi j hj=>h.product i j hi hj)
    refine ⟨?_,(Wc.restrictScalars ℝ).smul_mem s (show r • y∈Wc.restrictScalars ℝ from (Wc.restrictScalars ℝ).smul_mem r hx)⟩
    have hp:= binds_prod κ g Wc h.origin (fun i hi j hj=>h.product i j hi hj) (fun i hi j hj=>h.conductor i j hi hj) f p univ (fun i _=> (hz i).2) (fun i _=>(hz i).1) h.tide
    change Binds κ g (fun i=>s • r • (∏ j,f j i)) (fun i=>s • r • y i); simp_rw [← Complex.coe_smul s,← Complex.coe_smul r]; exact binds_pin κ g 0 _ _ (binds_pin κ g 0 _ _ hp _) _
lemma matte (χ:Chi)(V:Grid c)(u:Y.Wort)(hv:∀ i v,Summable (honest (align Y (Γ i)) χ v)) :
    Binds κ g (fun i=> (U i).mission χ (gauge T0 V) u) (fun i=>(U i).mission χ V u) ∧ (fun i=> (U i).mission χ V u) ∈ Wc:=by
    let f (v:Grid c)(j:Y.ShellK)(i:FI):= samples Y.lightF ((U i).duskV χ v) ((U i).dawnV χ v) j
    let S(v:Grid c):=wagon Y.broad u ∧ RG.flags (Pressure.temp τ) v∩GasP.wound Y.broad u = GasP.sweep Y.invD u
    have he (i:Option I) (V:Grid c): (align Y (Γ i)).mission χ V u= if S V then ∏ j∈u,f V j i else 0:=by
       unfold Fleet.mission motto; split; next hz=> rw [if_pos (show S V from ?_)]; rfl; exact hz
       next hp=> rw [if_neg (show ¬S V from hp)]
    have hz:S (Lattice.gauge T0 V)=S V:=by unfold S; rw [gauge_flags]
    simp_rw [he,hz]; split; swap; · exact ⟨unity κ g h.tide 0 0 (map_zero _),Wc.zero_mem⟩
    suffices H:∀ j∈u,Binds κ g (f (gauge T0 V) j) (f V j)∧ f V j∈ Wc from
       ⟨binds_prod κ g Wc h.origin (fun i hi j hj=>h.product i j hi hj) (fun i hi j hj=>h.conductor i j hi hj) (f (gauge T0 V)) (f V) u (fun i hi=> (H i hi).2) (fun i hi=> (H i hi).1) h.tide, gatheredX Wc _ _ (fun i hi=> (H i hi).2) h.origin (fun i hi j hj=> h.product i j hi hj)⟩
    rintro (j|j) hi; · exact turf Y Γ T0 h χ V j.val
    let Q(v:Grid c)(u:Clusters Y.Bright)(i:FI):=if GasP.seatP Y.lightF u=j then (U i).honest χ v u else 0
    have hP x: Binds κ g (Q (gauge T0 V) x) (Q V x)∧ Q V x∈Wc:=by unfold Q; split; exact atTerrace Y Γ T0 h χ V x; exact ⟨unity _ _ h.tide 0 0 (map_zero _),Wc.zero_mem⟩
    have hf(v i): f v (.inr j) i= NormedSpace.exp ( -(∑' x,Q v x i))-1:=by
       change GasP.dropsP Y.lightF _ _=_; unfold dropsP; unfold portion; apply congr_arg (fun t=>NormedSpace.exp (-t)-1); exact tsum_congr fun x=>by unfold Q GasP.seatP; rw [phoenix _ χ _ (h.earns i)]; rfl
    let T v:= fun i=>∑' x,Q v x i; have hS (v i): Summable (fun x=>Q v x i):= GasP.somG (hv i v|>.norm) _; let p:= alphabet κ g; let V':= gauge T0 V
    have hy:(T V',T V)∈p:= binds_tsum κ g (Q V') (Q V) (fun i=>(hP i).1) (hS V') (hS V)
    have hA:T V∈Wc:= entrance Wc (Q V) (fun i=> (hP i).2) (hS V)
    let x v i:= NormedSpace.exp (-T v i); have hp: (x V',x V)∈p:=
       binds_exp κ g Wc h.origin (fun i hi j hj=>h.product i j hi hj) (fun i hi j hj=>h.conductor i j hi hj) (x:=- T V') (y:=- T V) (p.neg_mem hy) h.tide (Wc.neg_mem hA)
    have hy:x V∈Wc:=toExp Wc (- T V) (Wc.neg_mem hA) (fun i hi j hj=> h.product i j hi hj) h.origin
    have ha: ((fun _:FI =>(1:P')),(fun _:FI=>(1:P')))∈p:=unity _ _ h.tide _ _ (map_one _)
    rw [show f V' (.inr j)=x V'-1 from funext (hf V'),show f V (.inr j)=x V-1 from funext (hf V)]; exact ⟨p.sub_mem hp ha,Wc.sub_mem hy h.origin⟩
end YM.QCD.Loom.Fleet.Palette
#print axioms YM.QCD.Loom.Fleet.Palette.matte
