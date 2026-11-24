import YM.QCD.Garden.Clay

/-! # Matrix jet linear transport: cover composition without period error -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f n:Side}{j k m:ℕ}{I:Type}{η σ r d C B:ℝ}
variable {P:Flight j k}{R:Columns P.L}{W:I→Bloom m}{X:Cnr f}{Y:Cnr c}{e:f.val=c.val*P.L.val} (hr:0≤η)(hp:(R none).strip η C)
local notation "g"=>sliceL P e
variable (hk:∀ b j x,(flux (arm su f 1 X)) b j x=∑ p:PlaqAxes,∑' y,R none ((sliceL P e).residue x,plaquette b) (plaquette p) y*flux (arm su c 1 Y) p j ((sliceL P e).parent x+wrap c y))
lemma pegmatite (M:Rail c f)(N:Rail f c)(W:Bloom m) (x : Cnr f) (p n : Site c):
    Run.cell (M*epilogue W x*N) p n= ∑ r:Site P.L,∑ i:Site c, Run.cell M p ((g).assemble (i,r))*cell (epilogue W x) ((g).assemble (i,r)) ((g).assemble (i,r)+wrap f (stop 0 W.tail))* cell N ((g).assemble (i,r)+wrap f (stop 0 W.tail)) n:=by
  rw [Matrix.mul_assoc M,cell_mul]; let g':= sliceL P e
  rw [← Equiv.sum_comp g'.splitSites.symm, Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro r _; apply sum_congr rfl; intro i _; rw [cell_mul]; let v:= g'.assemble (i,r); let w:=wrap f (stop 0 W.tail)
  change cell M p v * (∑ y, cell (epilogue W x) v y*cell N y n)=_ -- parse
  rw [sum_eq_single (v+w),← Matrix.mul_assoc]
  · intro y _ hy; rw [whereRay,if_neg hy.symm,zero_mul]
  simp

include hr hp hk
lemma tray_model (A:Plan j)(hj:4≤j)(hq:4≤k)(hs:Fractal W σ B)(ht:Fractal (tray P R W) r d):
    (∑' i: Tin P m I, epilogue (tray P R W i) Y) =barP P e*(∑' i:I,epilogue (W i) X)*proton P e:=by
  let Q:=tray P R W; let T(z):= epilogue (Q z) Y; let M:= barP P e; let N:=proton P e
  have hT:= bough ht Y; have hh (x y:Site c):cell (∑' i,T i) x y= ∑' i,cell (T i) x y:= ((cellC x y).hasSum hT.of_norm.hasSum).tsum_eq.symm
  let Z: Sheet f→L[ℂ] Sheet c:= LinearMap.toContinuousLinearMap { toFun:=fun X=> M*X*N,map_add':=fun X Y=>by rw [Matrix.mul_add, Matrix.add_mul],map_smul':=fun a b=> by rw [Matrix.mul_smul,Matrix.smul_mul]; rfl }
  have he x y : cell (M*(∑' i,epilogue (W i) X)*N) x y=∑' i,cell (M*epilogue (W i) X*N) x y:= ((cellC x y).hasSum (Z.hasSum (bough hs X).of_norm.hasSum)).tsum_eq.symm
  ext ⟨p,a⟩ ⟨n,b⟩; change Run.cell (∑' i,T i) p n a b=Run.cell (M*(∑' i,epilogue (W i) X)*N) p n a b; rw [hh,he]; apply congr_arg (fun B:Bundle=>B a b); -- change?
  let V (i):=Run.cell (T i) p n; have hu : Summable fun i=>‖V i‖:= hT.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>cell_pay ..)
  change (∑' i,V i)=_; rw [hu.of_norm.tsum_prod]; apply tsum_congr; intro i
  rw [pegmatite (P:=P) (e:=e), (hu.of_norm.prod_factor _).tsum_prod,tsum_fintype]; refine sum_congr rfl fun r _=> block_eq (W i) r hr hp hk A hj hq p n ((hu.prod_factor _).prod_factor r)
end YM.QCD.Garden
