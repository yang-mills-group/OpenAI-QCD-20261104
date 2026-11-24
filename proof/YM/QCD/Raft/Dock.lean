import YM.QCD.Raft.Port

/-! # L-scale α identification. full formula is along prepared finite links. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat Flume Exterior
open YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v r a b C D t s G:ℝ}
variable (P:Plan j)(L:Plan k)(V:Back E K j k p u v) (R:Avenue V η Ω Θ) {X:On}{Y:On}
-- association of aliases/signals.
def smokeSig (he:0<η): Signal (V.chain.n) (localG V) R.D R.D' R.T η Ω Θ R.s where
 more:=he
 extraZ:=R.begun
 deep:=R.coins
 roof:=R.price
 floorP:=R.nextP
 sizes i:= (anchor V i).sizes
 goes:= by
   refine tendsto_atTop.2 (fun n=>?_); exact (V.chain.cofinal.eventually_ge_atTop n.val)
 diag i:= by obtain ⟨_,_,h⟩:= R.floorP i; exact h.diagonalInv
 valid i:= (R.stays i).stays
 parity:= V.fly.odd
 harmony:=(R.paidUp 0).tide

lemma cabinet (i)(a:su.Color)(x: Exterior.form 1 (V.chain.n i)): ∃ p: BaseSites su (localG V i), Garden.rise (V.port.forest i) R.T (career _ 1 a x)=career _ 1 a (installed (anchor V i).ratio R.T.A0 *ᵥ x)-gradientA su _ p:=by
  let H:= V.port.forest i; let g:= (anchor V i).ratio; let T:= installed g R.T.A0; let M:= Precision.extracted (anchor V i) H T; let P:= career (V.chain.n i) 1 a; let z:=arm su _ 1 (P x)
  let Y:=(Precision.straighten (anchor V i) H T)*ᵥ x; let F:= localG V i
  refine ⟨-career F 0 a Y,?_⟩
  have hp : Garden.rise H R.T (P x)=career F 1 a (M *ᵥ x):=by
    apply (arm su _ 1).injective; unfold rise; rw [ContinuousLinearEquiv.apply_symm_apply]; ext ⟨u,v⟩ j
    have he := Work.F04.parts_stretch (S:=anchor V i) H T z j
    rw [show parts su 1 z j=a j • x from packsG .., Matrix.mulVec_smul] at he
    exact congr_fun he (u,v)
  have hm:M *ᵥ x=T *ᵥ x+Exterior.d 0 F *ᵥ Y:=by unfold M Precision.extracted; rw [add_mulVec,← Matrix.mulVec_mulVec]
  rw [show rise _ _ _=_ from hp,hm,map_add,colored_G,map_neg,sub_neg_eq_add]

lemma rentG (i)(A:su.Color)(he:0<η) (ha:Vital X)(hb:Vital Y)(hh:Tender (V.charge P L X i) (castF (Y _)) 3)(hp:ContDiffAt ℝ ω (purchaseG V P X i) 0):
    let z:=pointT (V.chain.n i) 1
    let u:=scoreM (rollG P V.fly.wing X _) A (expandG (smokeSig V R he) i z)
    u =scoreM (purchaseG V P X i) A z+ scoreM (rollG L V.fly.land Y _) A z:=by
  intro z u
  have hi:= tree_toll P L V i R ha hb hh hp
  let p:= (V.chain.n i); let n:= localG V i; let g:Ratio p n:=(anchor V i).ratio
  let T:= installed g R.T.A0
  let M:=rollG P V.fly.wing X n; have hM: Loves M:= rigL P V.fly.wing X ha _
  let q v:=career p 1 A v; let f v:=career n 1 A v; let Y' v:= f (T *ᵥ v)
  have ht (v:Exterior.form 1 p): Jacobi.mixed (Y' v) (Y' v) M 0 = Jacobi.mixed (q v) (q v) (purchaseG V P X i) 0+ Jacobi.mixed (q v) (q v) (rollG L V.fly.land Y _) 0:=by
    obtain ⟨k,hk⟩:=cabinet V R i A v; rw [← flatten hM k k,show Y' v-_= _ from hk.symm]; exact hi _
  unfold u; rw [ratedP _ hM.peak,ratedP _ hp,ratedP _ (rigL L V.fly.land Y hb _|>.peak)]
  let a:= vision z; let b:= desire z
  rw [show (brace (expandG _ _ _) A).1=Y' a from congr_arg f (see T z),show (brace (expandG _ _ _) A).2=Y' b from congr_arg f (believe T z),ht,ht]
  rw [show q a=(brace z A).1 from rfl,show q b=(brace z A).2 from rfl]; unfold p; abel
end YM.QCD.Raft
