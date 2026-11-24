import YM.QCD.Garden.Pan

/-! # gauges and linear inheritance at this cover winding -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {n c f L:Side}{j k m:ℕ}{η σ B C A:ℝ}

lemma whereRay (W: Bloom m)(x : Cnr n)(i y:Site n):cell (epilogue W x) i y=if i+wrap n (stop 0 W.tail)=y then (occ i (stop 0 W.tail)) • lepton W x i else 0:=by
  ext a b; change entryR (U:=1) _ _ _ _ = _; unfold entryR; dsimp only; rw [wrap_stop]; split; swap; rfl
  rw [rack,occ_rays,Matrix.mul_smul,Matrix.mul_one]
lemma port_rate (g:Ratio c f)(h:Odd g.count.val)(x:Site c)(u:Cover): occ (g.embed x) (g.count.val • u)=occ x u:=by
  let p:Site c:=0; let v:=twins g p 0
  let a:ℂ:=(g.count.val:ℂ)⁻¹^2
  have he y:Free.scarf v (g.embed y)=a*Free.scarf p y:=welcome g h p 0 y
  have hh: g.embed x + wrap f (g.count.val • u)= g.embed (x+wrap c u):=by rw [← Ratio.embed_wrap]; exact (g.root.map_add ..).symm
  have hx : mode (tuning v) (g.count.val • u)=mode (tuning p) u:=by unfold v; rw [full_tune g h,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one]
  have hp:=concord v (g.embed x) (g.count.val • u); rw [hh,he,he,hx,mul_assoc a,← concord, mul_left_comm] at hp
  exact mul_right_cancel₀ (scarf_ne p (x+wrap c u)) (mul_left_cancel₀ (pow_ne_zero _ (inv_ne_zero (side_ne g.count))) hp)

lemma signX (g:Ratio c f)(h:Odd g.count.val)(x:Site c)(r:Site g.count)(d u v:Cover):
    let w:=x+wrap c u; let p:=Work.F08.carry r d; let y:=x+wrap c p
    let b:=arrives r d
    (occ (g.embed x) (lift r)*occ x u)* occ (g.assemble (x,r)) d*(occ (g.embed y) (lift b)*occ y v)=occ w (p+v-u):=by
  intro w p y b
  let A:=occ (g.embed x); let α:=occ w
  let D: Site f:=g.assemble (x,r); let a:=A (lift r); let S:=occ x u; let T:=occ x (p+v)
  let V:=occ (g.embed y) (lift b); let M:=occ y v
  have hx : g.embed x + wrap f (g.count.val • p) = g.embed y:=by rw [← g.embed_wrap]; exact (g.root.map_add ..).symm
  have he:a*occ D d=occ x p*V:=by
    rw [← port_rate g h,show a*occ D d=A (lift r+d) from (sign_rate ..).symm, show lift r + d = _ from ((carry_spec r d).trans (add_comm _ _)), show A (_+_) = _ from (sign_rate ..)]
    rw [hx]
  change a*S*occ D d*(V*M)=_
  calc
    _= S*(a*occ D d)*V*M:=by ring
    _= S*T:=by rw [he,mul_assoc S (occ x p * V),mul_assoc (occ x p),show V*V=1 from (realSeam ..).2, mul_one,mul_assoc S,show occ x p*M=T from (sign_rate ..).symm]
    _= _:=by
      have hy : S*occ w (p+v-u)=T:= (sign_rate ..).symm.trans (congr_arg (occ x) (by abel : u+(p+v-u)=p+v))
      rw [← hy,← mul_assoc, show S*S=1 from (realSeam ..).2,one_mul]

-- isolated colour flux resummation via a rectangular tensor of infinite cover paths
variable {P:Flight j k} {R:Columns P.L} (W:Bloom m) (r:Site P.L)(x : Site c)
variable {X : Cnr f}{Y:Cnr c}{e:f.val=c.val*P.L.val}(hr:0≤η)(hp:(R none).strip η C)
variable (hk:∀ b j x, (flux (arm su f 1 X)) b j x= ∑ p:PlaqAxes,∑' y,R none ((sliceL P e).residue x,plaquette b) (plaquette p) y*flux (arm su c 1 Y) p j ((sliceL P e).parent x+wrap c y))
private def contentY (Y:Cnr c)(s:RG.Slot) (x: Site c)(r:Site L)(t : PlaqAxes)(z:Cover):=
      faceCurl (x+wrap c (Work.F08.carry r s.offset+z),t) (arm su c 1 Y)

include hk hp hr
lemma assemble_pays (u v : Cover): HasSum (fun z:Address m=> lepton (jar P R W r (u,v,z)) Y (x+wrap c u)) (colourPot P W r u v (lepton W X ((sliceL P e).assemble (x,r)))) :=by
  let A (b i): Cover→ℝ:= mer R W r b i
  let M (b i y) := contentY Y (W.petals i) x r b y
  let funP b c i (y:Cover):ℝ:= A b i y * M b i y c
  let Z:=arm su c 1 Y
  let S:=sliceL P e; let q:=S.assemble (x,r)
  have hx i j: faceCurl (slotFace (W.petals i) q) (arm su f 1 X) j=∑ p:PlaqAxes,∑' y,funP p j i y:=by
    unfold slotFace; rw [add_comm]; rw [show faceCurl (_+_,_) (arm su f 1 X) j=_ from hk ..]; refine sum_congr rfl fun k _=>?_
    refine tsum_congr fun y=>?_; unfold funP M contentY; simp only [moves_parent,S,q,Ratio.assemble_parent,Ratio.assemble_res,map_add,← add_assoc]; rw [Ratio.residue_wrap]; unfold A mer Work.F08.arrives; simp only [map_add,wrap_lift]; rfl
  have hz (i b z u) : faceCurl (slotFace (slot (distend (W.petals i) r u z) b) (x+wrap c u)) (arm su c 1 Y) = M b i z :=by
    unfold M contentY slotFace distend; simp only [slot_offset,slot_plaq,map_sub]; congr 2; abel
  let g (i:Address m)(j:Fin m→su.ColorIndex):ℝ:= ∏ l,funP (i.1 l) (j l) l (i.2 l)
  have hf b i j:Summable fun y=>|funP b j i y|:=by
    have h : Width η C (A b i):= hp _ _
    unfold funP; simp_rw [abs_mul]
    have hT y: |M b i y j|≤ ∑ w:Site c, |faceCurl (w,b) Z j|:=single_le_sum (fun w _=>abs_nonneg (faceCurl (w,b) Z j)) (mem_univ _)
    refine (((h.unweighted hr).2.1.mul_right (∑ w:Site c, |faceCurl (w,b) Z j|))).of_nonneg_of_le (fun u=> by positivity) fun u=> mul_le_mul_of_nonneg_left (hT u) (abs_nonneg _)
  let T (d:Fin m→su.ColorIndex):=∏ i,faceCurl (slotFace (W.petals i) q) (arm su f 1 X) (d i)
  have hG (d : Fin m→su.ColorIndex): HasSum (fun p:Address m=> g p d) (T d):=by
    have h (b:Fin m→PlaqAxes) := Iteration.Cost.tsum_pi (fun i=> hf (b i) i (d i))
    have he: Summable (fun p:Address m=>g p d):=by
      apply Summable.of_norm; exact (summable_prod_of_nonneg (fun u=> norm_nonneg _)).2 ⟨fun k'=> (h k').1,Summable.of_finite⟩
    convert! he.hasSum using 1; rw [he.tsum_prod,tsum_fintype]; unfold T; simp_rw [hx,Fintype.prod_sum]; refine sum_congr rfl fun i _=> (h i).2.symm
  let K(d : Fin m→su.ColorIndex):=colourPot P W r u v (W.coeff d)
  have hl z : lepton (jar P R W r (u,v,z)) Y (x+wrap c u)=∑ d,g z d • K d:=by
    unfold lepton Bloom.hues; refine sum_congr rfl fun j _=>?_; unfold jar; dsimp only; simp_rw [hz,smul_smul]
    rw [show g z j • K j=((g z j:ℝ):ℂ) • K j from rfl, mul_comm]; congr 1; unfold g brew funP; rw [prod_mul_distrib,Complex.ofReal_mul]
  have hh : colourPot P W r u v (lepton W X q)=∑ j,T j • K j:=by unfold lepton Bloom.hues colourPot K; rw [Matrix.mul_sum, Matrix.sum_mul]; refine sum_congr rfl fun i _=>?_ ; rw [Matrix.mul_smul,Matrix.smul_mul]; rfl
  change HasSum _ (colourPot P _ _ _ _ (lepton W X q)); simp_rw [hl]; rw [hh]; exact hasSum_sum (fun i (_:i∈univ)=> (hG i).smul_const (K i))
end YM.QCD.Garden
