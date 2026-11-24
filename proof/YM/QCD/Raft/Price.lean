import YM.QCD.Raft.Cliff

/-! # uniform total price across ANY history interval. 

Clock with one parameter j. Uses arbitrarily extended auxiliary torus to assess; not at current cutoff. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Flume Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a b c C D s G α g h w:ℝ}
variable (P:Plan j)(L:Plan k)(V:Back E K j k p u v) (R:Avenue V η Ω Θ)
lemma deed (A:su.Color)(Y: Offer 1 a b)(X:Offer 2 r c)(y: Offer 1 g h)(x:Offer 2 w D)(U Z: Ornament t C)(ha:‖A‖=1)(h1:0<a)(hb:0 ≤b)(h2:0<r)(hc:0≤c)(ht:0<t)(hv:t≤η/2)(hη:0<η)
    (hh:∀ i,Tender (V.charge P L (mingle Y X) i) (castF ((mingle y x) _)) 3)(hk:0<s)(hG:0≤G)(hp: Skies P V (mingle Y X) R.D' U.page Z.page α s G):
    Tendsto (fun i=> readP (rollG P V.fly.wing (mingle Y X) (localG V i)) A-readP (rollG L V.fly.land (mingle y x) (V.chain.n i)) A) atTop (𝓝 α):=by
  let Y':= mingle Y X; let Z':=mingle y x
  have hY: Vital Y':= Y.bright.add X.bright; have hZ:Vital Z':= y.bright.add x.bright
  obtain ⟨z,H⟩:= inheritG V R U hη ht hv
  have h':= smokeSig V R hη
  obtain ⟨W,hW⟩:=boundUp P A h1 h2 hb hc
  obtain ⟨D, Hd⟩:= calibrated (c:=b) (d:=c) P A ha h1 h2
  let X' i:= rollG P V.fly.wing Y' (localG V i)
  have he := oceanH (P:=X') h' (fun i=> rigL P _ _ hY _) R.merits (fun i=> (R.stays i).trial) ⟨W,((horizonG h').eventually hW).mono fun i hi=> hi Y X _⟩ ⟨Pearl.chargeF,D,((horizonG h').eventually Hd).mono fun i hi=> hi Y X _⟩
  let v:=profG P V A Y'
  have hu:= ferry P V R hp A ha hη ht hv hk hG; have hM:= hu.sub he; rw [sub_zero] at hM; refine hM.congr' (Eventually.of_forall fun i=>?_)
  have hS:= rentG P L V R i A hη hY hZ (hh i) (unilink P V R hp H i)
  unfold X' at *; dsimp only [profG] at *; rw [show scoreM (rollG P V.fly.wing Y' (localG V i)) _ (expandG _ _ _)= _ from hS]
  unfold readP supS scoreM at *; unfold Y' Z'; ring
end YM.QCD.Raft
