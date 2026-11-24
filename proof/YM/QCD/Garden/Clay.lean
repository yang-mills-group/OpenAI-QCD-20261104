import YM.QCD.Garden.Pays

/-!
# absolute label placement into two ends. exact through born jet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f n:Side}{j k m:ℕ}{η C:ℝ}
variable {P:Flight j k}{R:Columns P.L}(W:Bloom m)(r:Site P.L)
variable {X:Cnr f}{Y:Cnr c}{e:f.val=c.val*P.L.val} (hr:0≤η)(hp:(R none).strip η C)
local notation "g"=>sliceL P e
variable (hk:∀ b j x,(flux (arm su f 1 X)) b j x=∑ p:PlaqAxes,∑' y,R none ((sliceL P e).residue x,plaquette b) (plaquette p) y*flux (arm su c 1 Y) p j ((sliceL P e).parent x+wrap c y))

lemma unwind (x: Site c)(d: Cover):(g).assemble (x,r)+wrap f d=(g).assemble (x+wrap c (Work.F08.carry r d),arrives r d):=by
  rw [moves_site (sliceL P e), Ratio.assemble_parent,Ratio.assemble_res]; -- issue looping!

-- sums conditional x indicator. using reanchor points

def printedF (Y:Cnr c)(W:Bloom m)(R: Columns P.L)(r:Site P.L)(p n x:Site c)(u v:Cover)(z:Address m):= if x+wrap c u=p then Run.cell (epilogue (jar P R W r (u,v,z)) Y) p n else 0

def packetF (X:Cnr f)(P:Flight j k)(e:f.val=c.val*P.L.val)(W:Bloom m)(r : Site P.L)(p n x:Site c)(u v:Cover):Bundle:=
  let d:=stop 0 W.tail
  let y:= x+wrap c (Work.F08.carry r d)
  let i:=arrives r d
  let z:=(sliceL P e).assemble (x,r)
  caption P e (unFork P r u) x p r u *Run.cell (epilogue W X) z (z+wrap f d)*caption P e (fork P i v) y n i v

include hk hr hp
lemma packet_eq (p n x:Site c)(u v : Cover): HasSum (printedF (P:=P) Y W R r p n x u v) (packetF X P e W r p n x u v):=by
  let w:=x+wrap c u; let d:= stop (0:Cover) W.tail; let D:=probeEnd W.tail r u v; let y:=x+wrap c (Work.F08.carry r d); let i:= arrives r d; let s:=sliceL P e; let Z:=s.assemble (x,r)
  have hx : w+wrap c D=y+wrap c v:=by simp only [D,w,probeEnd,y,d,map_sub,map_add]; abel
  have heq z : stop (0:Cover) (jar P R W r (u,v,z)).tail=D:= rad_plan _
  by_cases h:w=p
  swap
  · have he:printedF (P:=P) Y W R r p n x u v=fun _=>0:=funext fun z=> if_neg h
    rw [he]; unfold packetF; rw [caption,if_neg h]; simp only [zero_mul]; exact hasSum_zero
  subst p
  let A:=unFork P r u; let B:= fork P i v; let J:=lepton W X Z; let q:=occ w D
  unfold printedF packetF; simp only [if_pos (show x+wrap c u=w from rfl), whereRay,heq,hx]
  change HasSum (fun z:Address m=> if y+wrap c v=n then q • lepton (jar P R W r (u,v,z)) Y w else 0) (caption P e A x w r u*(if True then occ Z d • J else 0)*caption P e B y n i v)
  by_cases ht:y+wrap c v=n
  · simp only [caption,if_true,if_pos ht, if_pos (show x+wrap c u=w from rfl)]; rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,Matrix.smul_mul,smul_smul,smul_smul]; -- inspect
    have hh:= (assemble_pays W r x hr hp hk u v).const_smul q
    convert hh using 2; unfold q D w; rw [show occ _ (probeEnd W.tail r u v)=_ from (signX s P.odd x r d u v).symm]; unfold y i; ring
    rfl
  simp only [caption,if_true,if_neg ht,mul_zero]; exact hasSum_zero

lemma block_eq (A:Plan j)(hj:4≤j)(hL:4≤k)(p n: Site c) (he: Summable fun i:Note m=> ‖cell (epilogue (jar P R W r i) Y) p n‖):
    (∑' i:Note m, Run.cell (epilogue (jar P R W r i) Y) p n)=
    ∑ x : Site c, Run.cell (barP P e) p ((g).assemble (x,r))*cell (epilogue W X) ((g).assemble (x,r)) ((g).assemble (x,r)+wrap f (stop 0 W.tail))*cell (proton P e) ((g).assemble (x,r)+wrap f (stop 0 W.tail)) n:=by
  let Z(x : Site c)(i:Note m):=printedF (P:=P) Y W R r p n x i.1 i.2.1 i.2.2
  let G:=sliceL P e
  have ha x : Summable (Z x):= by
    apply Summable.of_norm; refine he.of_nonneg_of_le (fun _=>norm_nonneg _) (fun v=>?_); unfold Z printedF; split; · exact le_refl _
    rw [norm_zero]; exact norm_nonneg _
  have hh (i : Note m): Run.cell (epilogue (jar P R W r i) Y) p n=∑ x,Z x i:=by
    rw [sum_eq_single (p-wrap c i.1)]; unfold Z printedF; rw [if_pos (sub_add_cancel p _)]; intro w _ h; have he : w+wrap c i.1≠ p:=fun t=> h (eq_sub_of_add_eq t); exact if_neg he; simp
  simp_rw [hh,Summable.tsum_finsetSum (fun x _=> ha x)]; apply sum_congr rfl; intro x _
  let d:=stop (0:Cover) W.tail; let z:=G.assemble (x,r); let y:=x+wrap c (Work.F08.carry r d); let i:=arrives r d
  let M:= Run.cell (epilogue W X) z (z+wrap f d)
  have hu (u v:Cover): (∑' l:Address m,Z x (u,v,l))=packetF X P e W r p n x u v:= (packet_eq W r hr hp hk p n x u v).tsum_eq
  rw [(ha x).tsum_prod]; simp_rw [((ha x).prod_factor _).tsum_prod, hu];
  let N:= cell (proton P e) (z+wrap f d) n
  have he v : (∑' l,packetF X P e W r p n x v l)=caption P e (unFork P r v) x p r v*M*N:=by
    have hh: z+wrap f d=G.assemble (y,i):=unwind ..
    unfold N; rw [hh]; exact ((pepper y n i hj hL).mul_left _).tsum_eq
  simp_rw [he]; exact (((unPepper x p r A hj hL).mul_right M).mul_right N).tsum_eq
end YM.QCD.Garden
