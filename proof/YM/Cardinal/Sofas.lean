import YM.Cardinal.Solitaire
/-! # Singleton report tape, parity generalized. With mask bill requiring on-mask sizes only. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
namespace Card
namespace Iris
variable {q:Bool} (N)(o:Site c)
local notation "M"=> Ribbon.ample N Unit
local notation "T"=> topM
local notation "Vk"=> goldM q
local notation "K"=> Keys c N
local notation "R"=> Spine Iris.alpha
local notation "B!"=>Patio (Keys c N ⊕ Spine Unit)
local notation "p!"=>pluck K (goldM q)
set_option quotPrecheck false
open QCD.Stew
namespace Puff
variable (G:Puff c N J q)(P:BudgetPoint)(e:ℝ)(f:J→Support c)(hv:∀ i,f i⊆(G.addr i).support) (hw:1 ≤ e)
local notation "r'"=> (fun _:alpha=>q)
local notation "p'"=> (fun _:alpha=>o)
local notation "b'"=>banknote N (fun _:alpha=>o) e
local notation "d'"=>withdraw N (fun _:alpha=>o) e
noncomputable def stool (s:J→ℂ): Ruby.Hue c (ample N Unit) J:=⟨fun i=>(G.addr i).support,fun i U=> s i • ((masked P.threshold (f i) (fun V=> banknote N (fun _:Unit=>o) e ((G.roll).mark i V)) U) - masked P.threshold (G.addr i).support (fun V=> banknote N (fun _:Unit=>o) e ((G.roll).mark i V)) U)⟩
variable (s:J→ℂ)(Xb:Puff.Seal N o G)
local notation "Y!"=> stool N o G P e f s
include Xb
set_option maxRecDepth 6000 in
lemma foyer (i:J) (S:Support c): shadeG (masked P.threshold S (fun V=> b' ((G.roll).mark i V))):=by
    have ht:= G.declare N o Xb; let F V:= (G.roll).mark i V; let p:=b'; let y:=(G.addr i).support
    intro U V; let X:= masked P.threshold S (fun z=> p (F z)); refine congr_arg Subtype.val (?_ : sways (Lat.rotates (ample N Unit) V) (masked P.threshold S (fun z=>p (F z)) (gauge V U))=masked P.threshold S (fun z=>p (F z)) U); have hp:sways _ (p (F (Lattice.gauge V U)))=p (F U):= (across N p' e r' _ V (F _) (ht.stage i _).1).symm.trans (congr_arg b' (ht.tint i U V)) -- b', parentheses
    by_cases he: Healthy P.threshold S U
    · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (show Healthy _ _ _ from (by unfold Healthy at *; rw [gauge_flags]; exact he))]; exact hp
    rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (show ¬ Healthy _ _ _ from (by unfold Healthy at *; rw [gauge_flags]; exact he))]; exact map_zero _
omit Xb
lemma muting (φ:ℝ)(S:Support c)(x:Grid c)(i:J)(hp:0<e): withdraw N (fun _:alpha=>o) e (masked φ S (fun V=> b' ((G.roll).mark i V)) x)= masked φ S ((G.roll).mark i) x:=by
   by_cases h: Healthy φ S x; · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h,Cupola.home _ _ _ hp]
   rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,map_zero]
lemma sneering (C0:Support c)(i:J) (p:Grid c)(u:ℝ)(hp: 0<e): Mint N p' e r' T (masked u C0 (fun V=> b' ((G.roll).mark i V)) p):=by
   by_cases h: Healthy u C0 p; · rw [masked_eq _ _ _ _ h]; exact Mint.initiate T hp _ (worthE N q _ (G.beams i) _)
   rw [masked_ne _ _ _ _ h]; exact Mint.none _
include Xb hv
lemma paidSize (z:J→ℝ)(h:∀ i,0 ≤ z i)(hq:∀ i V, Healthy P.threshold (f i) V→load (fun _=>e) (G.fill i V) ≤ z i)(hp:Ac.Hit (fun i=>(G.addr i).support) P.B (fun i=>‖s i‖*z i) a A)(ht:0<e): Wax (stool N o G P e f s) P.threshold P.B a A e ∧ (∀ i,shadeG ((stool N o G P e f s).mean i))∧ (∀ i V,Mint N p' e r' topM ((stool N o G P e f s).mean i V)):=by
     have hK:= G.declare N o Xb; let L i (V:Grid c):= b' ((G.roll).mark i V); let v:=L; let χ (i:J) (C0:Support c):= masked P.threshold C0 (L i); have hL(i:J):LocalOn (G.addr i).support (L i) :=fun x V he=> congr_arg b' (hK.room i x V he); have hM(i:J)(C0:Support c): Measurable (χ i C0):= masked_measurable _ _ _ ((b').toLinearMap.toContinuousLinearMap.continuous.measurable.comp (hK.permit i)); have hS(i:J)(V:Grid c)(S:Support c): Gated (G.addr i).support (χ i S V):=by
         unfold χ; by_cases h:Healthy P.threshold S V; · rw [masked_eq _ _ _ _ h]; exact charged N o _ _ (G.beams i) (G.addr i).support (Xb.sees i) e ((Xb.anchor i) ▸ (G.addr i).anchor) V
         rw [masked_ne _ _ _ _ h]; exact Fleet.spruce _
     refine ⟨⟨⟨fun i x V h hx=> congr_arg (s i • ·) (congr_arg₂ (·-·) (High.keen (hv i) P.threshold _ (hL i) x V h hx) (High.keen (Subset.refl _) P.threshold _ (hL i) x V h hx)), fun i=>show Measurable (fun V=> s i • (χ i (f i) V- χ i (G.addr i).support V)) from Measurable.const_smul ((hM i (f i)).sub (hM i (G.addr i).support)) (s i),fun i U hx ht=> hx ?_,fun i U=>?_⟩,_,hp,fun i U=>?_⟩,fun i U k=>?_,fun i V=>?_⟩
     · change s i • (masked _ _ _ _ - masked _ _ _ _) =_; rw [masked_eq (P.threshold) (G.addr i).support _ _ ht,masked_eq _ _ _ _ (Finset.disjoint_of_subset_left (hv i) (show Healthy P.threshold (G.addr i).support U from ht)),sub_self,smul_zero]
     · change light _ (s i • (χ i (f i) U - χ i (G.addr i).support U))∈_; rw [map_smul]; exact Subalgebra.smul_mem _ (wingsZ _ _ _ (hS ..) (hS ..)) _
     · rw [tokenCC]; change ‖tokenC e (s i • (χ i (f i) U - χ i (G.addr i).support U))‖ ≤ _; rw [map_smul,norm_smul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
       unfold χ; by_cases he:Healthy P.threshold (G.addr i).support U; · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (he.mono_left (hv i)),sub_self,map_zero,norm_zero]; exact h i
       rw [masked_ne _ _ _ _ he,sub_zero]; by_cases he: Healthy P.threshold (f i) U; · rw [masked_eq _ _ _ _ he]; have hp:=Iris.charge N o q ((G.roll).mark i U) (worthE N _ _ (G.beams i) _) e ht; exact hp.trans_le (by rw [show pluck K Vk ((G.roll).mark i U)=G.fill i U from worthG _ _ _ (G.beams i) U]; exact hq i U he)
       rw [masked_ne _ _ _ _ he,map_zero,norm_zero]; exact h i
     · let g:= sways (Lat.rotates M k)
       have hp(C0:Support c): g (χ i C0 (Lattice.gauge k U))=χ i C0 U:=Subtype.ext (foyer N o G P e Xb i C0 U k)
       refine congr_arg Subtype.val (?_ : g (s i • (χ i (f i) (Lattice.gauge k U) - χ i (G.addr i).support (Lattice.gauge k U)))=s i • (χ i (f i) U-χ i (G.addr i).support U)); rw [show g (s i • (χ i (f i) (Lattice.gauge k U) - χ i (G.addr i).support (Lattice.gauge k U)))=s i • g (χ i (f i) (Lattice.gauge k U) - χ i (G.addr i).support (Lattice.gauge k U)) from swayC _ _ _,map_sub,hp,hp] -- g alg? issue
     · let g:= trophy N p' e r' ({topM}:Set (Finset Unit)); let w₀:=χ i (f i) V; let w₁:= χ i (G.addr i).support V; have hx:=sneering N o G e (f i) i V P.threshold ht; have hz:=sneering N o G e (G.addr i).support i V P.threshold ht
       apply (Mint.gauge ht).mpr; -- g scalars ℂ via lift
       let Gc: EvenA c M→L[ℂ] EvenA c M:= (b').toLinearMap.toContinuousLinearMap.comp ((slash K r' {topM}).comp ((d').toLinearMap.toContinuousLinearMap))
       change Gc (s i • (w₀-w₁))=s i • _; rw [map_smul,map_sub,show Gc w₀=w₀ from (Mint.gauge ht).mp hx,show Gc w₁=w₁ from (Mint.gauge ht).mp hz]
end Puff
end Iris
end Card
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Card.Iris.Puff.paidSize
