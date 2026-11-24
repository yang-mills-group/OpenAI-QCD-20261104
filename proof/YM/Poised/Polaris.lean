import YM.Poised.Summum
import YM.Poised.Burden
/-! # Accuracy through any emitted panel, on admissible marker lookup. Bucket sizes charged from row moment signals on actual X and Y. No supra-leg values from Canon section needed in direction; eras funding below. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h)) (R:BudgetPoint)
variable (X:Support l)(Y:Support c)(b b':Cover) {u v w L N p r':ℕ} {τ σ t vo vi A C M ρ ε:ℝ}
variable {X Y b b'}
open QCD.Kites
variable (J:Labels.Jet su)(Vb:Hera.Rights su N)(H:TaperHol)(F:Grid l→ Lat.Fields l 6) (hf: Ease.Charm R X F) (hr:Rooted X F) (hR:∀ i, Mom.needed X i → width R (wrap l b) i ≤1) (hL:∀ U,F U∈layer (Faces (Site l)) p) (D':ℕ) (hX:R.supBounds (wrap l b) X ((Pipes.framesF (purseX (wrap l b) D' vi)) ∘ F) M)
-- notation conversions
lemma framed1 [Fintype B](Y:Alg B): framesF (fun _=>1) Y=Y:=by
    let S:Matrix B B ℂ:= Matrix.diagonal fun _=>(1:ℂ); change changeVars S _=_; rw [show S=(1:Matrix B B ℂ) from rfl,change_one]; rfl -- lemma name
include hr hf hX hL
local notation "JT"=> t • J
local notation "f!"=> fun i:ℕ=> actionT d i (X:=X) (b':=b') (Y:=Y) P h T H J vo t
local notation "J'"=> fun (i:ℕ)=> craftT d i (b:=b) (X:=X) (b':=b') P h T J vo t
local notation "r"=>wrap l b
local notation "Ft"=>purseX r D' vi
variable (ht: ∀ i≤d, Venture (Pipes.purseX (wrap l b) D' vi) (fun _=>1) (P:=R) (o:=wrap l b) C (craftT d i (X:=X) (b:=b) (b':=b') P h T J vo t))(hz: ∀ i≤ d,Venture (Pipes.purseX (wrap l b) D' vi) (fun _=>1) (P:=R) (o:=wrap l b) ε (actionT d i (X:=X) (Y:=Y) (b':=b') P h T H J vo t - craftT d i (X:=X) (b:=b) (b':=b') P h T J vo t))(hC:1 ≤ C)(hε:ε≤ C)(hv:0<ε)(hν:0<vi) (hn:n≤d)(hN:d<N)(hP:N ≤ R.order)
def ult (p:ℕ)(Vb:Hera.Rights su N) (C:ℝ) := C^N*Pipes.mouth (1+N+1) Vb N p
omit hr hf hX hL in
lemma ult_pos (hv:1≤ C)(p:ℕ) (W:Hera.Rights su N):0 ≤ ult p W C:=by unfold ult Pipes.mouth; have ht:=W.large; positivity
local notation "M0"=> ult p Vb C
set_option quotPrecheck false
local notation "W0"=> fun i:OrderedFinpartition n=>iteratedFDeriv ℝ i.length (lotsF F) 0 (J'∘i.partSize)
include hR ht hC hN hn hP hν
lemma up_cost (i:OrderedFinpartition n): ‖W0 i‖ ≤ M0*M:=by
   let Y':= framesF (fun _ : ZBand d=>1)∘ lotsF F; have he(Y):framesF (fun _ : ZBand d=>1) Y=Y:= framed1 _; have hY : Y'=lotsF F:=funext fun i=> he _
   let p':= fun j:Fin i.length=>J' (i.partSize j); let x:= (0:Pipes.Path l (ZBand d)); have he : 1 ≤ 1+ (N:ℝ):= le_add_of_nonneg_right (Nat.cast_nonneg _); let Q:=1+(N:ℝ); have hp:=i.length_le.trans (hn.trans hN.le)
   have hx :Healthy R.threshold X (increment 1 x.1):=by change Healthy _ _ (increment 1 0); rw [Work.G07.at_zero_increment]; exact Next.Foundations.one_healthy _ _ R.threshold_pos.le
   rw [←hY]; let v:= fun i:Fin i.length=> C; apply (risingW F x Ft (fun _ :ZBand d=>1) Vb hf hX (purse_pos _ _ _ hν) hx (fun j hj=>⟨(show ‖(0:su.Color)‖ ≤ 1 by simp),hR j hj⟩) p hL hp hP (show SeatD Ft _ (0: VectorD (Site l) (ZBand d)) 1 from ⟨zero_le_one,fun _=>by simp [orderR]⟩) p' v (fun _=>zero_lt_one.trans_le hC) (fun i'=>ht _ ((i.partSize_le i').trans hn))).trans
   let R' := Pipes.mouth (Q+1) Vb i.length p; have hz:0≤R':=by unfold R' Pipes.mouth; have h:=Vb.large; positivity
   simp only [v,prod_const,card_univ,Fintype.card_fin]; unfold ult; refine mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ hC hp) (bite Vb 1 le_rfl _ hp) hz (by positivity)) hX.1
-- issue .. R.S arguments ordering
include hz hv hε
lemma driftL : ‖iteratedDeriv n (engine vo (ZBand d) ∘ Beacon.moment H b' JT (kite P h T F Y)) 0 - (∑ i: OrderedFinpartition n,W0 i)‖ ≤ ((Fintype.card (OrderedFinpartition n):ℝ)* 2^N*ε*M0)*M:=by
   let Y':= framesF (fun _ : ZBand d=>1)∘ lotsF F; have he(Y):framesF (fun _ : ZBand d=>1) Y=Y:= framed1 _; have hY : Y'=lotsF F:=funext fun i=> he _
   let W:= (1+(N:ℝ)+1); let Z:= ult p Vb C; have hk : Healthy R.threshold X (1:Grid l):=Next.Foundations.one_healthy _ _ R.threshold_pos.le
   rw [legendary P h _ _ hr ((hf.smooth _ hk).of_le (Nat.cast_le.mpr (hN.le.trans hP))) H J hn, ← Finset.sum_sub_distrib,← hY]
   have heV: ∀ i:OrderedFinpartition n, ‖iteratedFDeriv ℝ i.length Y' 0 (fun j=> f! (i.partSize j))-iteratedFDeriv ℝ i.length Y' 0 (J' ∘ i.partSize)‖≤ (2:ℝ)^N*(ε*C^N*Pipes.mouth W Vb N p*M):=by
       intro i; let x:= (0:Pipes.Path l (ZBand d)); have hx: increment 1 x.1=1:= Work.G07.at_zero_increment 1; have hL:= alters (a:=p) F R X b x Ft (fun _=>1) Vb 1 ε le_rfl hv (hx.symm ▸ hk) (fun j hj=>⟨(show ‖(0:su.Color)‖ ≤ (1:ℝ) by simp),hR j hj⟩) hX hf hP (i.length_le.trans_lt (hn.trans_lt hN)) hL (purse_pos _ _ _ hν) hC (fun k=> ht _ ((i.partSize_le k).trans hn)) (fun i'=>hz _ ((i.partSize_le i').trans hn)) hε (show SeatD Ft (fun _=>1) (0:VectorD (Site l) (ZBand d)) 1 from ⟨zero_le_one,fun i=>by simp [orderR]⟩)
       exact hL
   apply (norm_sum_le ..).trans ((Finset.sum_le_sum fun i _=> heV i).trans_eq ?_); rw [sum_const,card_univ,nsmul_eq_mul]; unfold W ult; ring
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.up_cost
#print axioms YM.Massive.Poised.Chute.driftL
