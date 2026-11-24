import YM.QCD.Smoke.Bloom

/-! # site tallies -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Push.Uniform Run Tree RG
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Sparks Jacobi Extra Iteration Work.F03 Precision Bid Tavern
open scoped Topology Matrix Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {n N: Side} {r C d A:ℝ}
-- shifts including seam parity stay gauge
lemma spectra (s:Signed)(x:Cnr n): arm su n 1 (orderTurn s x)=pulled (arm su n 1 x) s:=by
  change arm su n 1 (flipCoords s ℝ x)= _; ext ⟨i,k⟩ j
  obtain ⟨k,rfl⟩ := axisEquiv.surjective k
  simp only [coord_map,Bid.pulled,show axisEquiv.symm (coord k)=k from axisEquiv.symm_apply_apply _,arm_apply,flip_price]
  unfold affine Step.used Step.rotate posDir; cases h : s.flip k <;> simp [h,arm_apply]
lemma roller (x:Cnr n)(s:Signed) : ‖orderTurn s x‖≤‖x‖:=by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; rintro ⟨p,y,i⟩
  obtain ⟨j,rfl⟩:=axisEquiv.surjective y
  change ‖flipCoords (m:=n) s ℝ x (p,coord j,i)‖≤ _; rw [flip_price]; split <;> first| exact norm_le_pi_norm x _ | rw [norm_neg]; exact norm_le_pi_norm x _
lemma towns (d:Site n)(x:Cnr n)(p:Road n): spaceShift d x p=x (p.1+d,p.2):=by
  rcases p with ⟨p,i,j⟩; rw [← arm_apply su n 1 (spaceShift d x),spaceAt]; rfl
lemma balloon (x:Cnr n)(b:Site n): ‖spaceShift b x‖≤‖x‖:=by apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; rw [towns]; exact norm_le_pi_norm x _
-- translated curl
lemma launched (x:Cnr n)(b:Site n)(t:PlaqAxes)(y : Site n)(j): faceCurl (y,t) (arm su n 1 (spaceShift b x)) j=faceCurl (y+b,t) (arm su n 1 x) j:=by
  -- use explicit plaquette
  let q:=Lattice.lift y; let p:=Lattice.lift b
  rw [show y= wrap n q from (wrap_lift ..).symm,← curl_read, show wrap n q + b=wrap n (q+p) from ?_, ← curl_read]; swap; · rw [map_add,show wrap n p=b from wrap_lift _]
  -- flux translated shift page
  have h (l:Walk)(c:Cover): bill (page (spaceShift b x) j) c l=bill (page x j) (c+p) l:=by
    induction l generalizing c with
    | nil=> rfl
    | cons i l ih=>
      rw [bill,bill,ih,add_right_comm c]; congr 1
      rcases i with ⟨i,t⟩; cases t <;> simp [Step.used,page,towns,map_add,p,sub_eq_add_neg,add_right_comm]
  exact h ..
lemma salesG (T:Atom su 2)(x:Cnr n)(b:Site n): (Iteration.plain T).sample (flux (arm su n 1 (spaceShift b x))) 0=(Iteration.plain T).sample (flux (arm su n 1 x)) b:=by
  simp only [Pattern.sample,flux,Iteration.plain,Iteration.read,Option.elim, launched x b]; simp [add_comm b]

def quiverG : (Wisp × (Fin 2→su.ColorIndex))≃Kite:=⟨fun p=>triangleG p.1 p.2,fun i=> (fun j=> ((i j).1,(i j).2.1),fun j=> (i j).2.2),fun _=>rfl,fun _=>rfl⟩
variable {S:SparkMesh}{T:Skyline S}{P:Planet}{m:ℕ→ℕ}
def flyG (P:Planet)(x:Fin 2→Cnr n)(p:Kite):ℝ:= (∏ i,idyllic (p i) (x i))* P p
lemma flyCost (he:Heaven S T r C P m)(hp:0 < r)(x:Fin 2→Cnr n): Summable fun p=>|flyG P x p|:=by
  let A:=2*‖x‖; apply ((home_run hp).mul_left (A^2*C)).of_nonneg_of_le (fun j=> abs_nonneg _) ; intro p
  have h (i:Fin 2): ‖idyllic (p i) (x i)‖ ≤ A*(1+timbre (exposed p)):=by
    let Z:Stock:=((p i).1,(p i).2.1); apply (paid_page (x i) (p i).2.2 0 (stanza Z)).trans
    have ht : (↑(stanza Z).length:ℝ)≤ 2* Laurent.size (p i).1+2:=by exact_mod_cast stanza_length Z
    have hv : Laurent.size (p i).1≤timbre (exposed p):= le_trans (single_le_sum (fun j (_:j∈univ)=>Nat.zero_le (Laurent.size (p j).1)) (mem_univ i)) (Nat.le_add_left ..)
    apply (mul_le_mul ht (norm_le_pi_norm x i) (norm_nonneg _) (by positivity)).trans; unfold A; rw [mul_right_comm (2:ℝ) ‖x‖]; gcongr; linarith [Nat.cast_le (α:=ℝ)|>.2 hv]
  unfold flyG; rw [abs_mul,Finset.abs_prod]; apply (mul_le_mul (prod_le_prod (s:=univ) (fun i _=> abs_nonneg _) (fun i _=> h i)) (he.ceiling p) (abs_nonneg _) ((prod_nonneg fun _ _=> by positivity))).trans_eq; rw [prod_const,card_univ,Fintype.card_fin]; ring
lemma fieldR (P:Planet)(x:Cnr n)(i:Wisp): ∑ a:Fin 2→su.ColorIndex, flyG P (fun _=> x) (triangleG i a)=∑ j:Wink i, 2*(Iteration.plain (strata P ⟨i,j⟩)).sample (flux (arm su n 1 x)) 0:=by
  let g (s:Fin 2)(j:Get (i s))(a) := (plant (i s) j).sign * faceCurl (slotFace (shop (plant (i s) j)) (0:Site n)) (arm su n 1 x) a
  have hx (a:Fin 2→su.ColorIndex): ∏ j,idyllic (triangleG i a j) x= ∑ q:Wink i,∏ j,g j (q j) (a j):=by
    rw [show ∏ j,idyllic (triangleG i a j) x=∏ j,∑ q:Get (i j), g j q (a j) from prod_congr rfl (fun j _=> field (triangleG i a j) x)]; exact Fintype.prod_sum _
  unfold flyG; simp_rw [hx, plain_flux,Atom.poly,strata,sum_mul,mul_sum]
  rw [Finset.sum_comm]; refine sum_congr rfl fun j _=>sum_congr rfl fun a _=>?_ ; simp only [signal,g,prod_mul_distrib]; norm_num; ring
lemma atm (he: Heaven S T r C P m)(hp:0<r)(hh:0≤d)(h:Charged (strata P) d A)(x:Cnr n): lotusG P (fun _=>x)=2*∑' p:Twig, (Iteration.plain (strata P p)).sample (flux (arm su n 1 x)) 0:=by
  let v (_:Fin 2):=x
  have ht:= sample_summable (Iteration.plain ∘ strata P) (flux (arm su n 1 x)) hh h 0
  unfold lotusG; change (∑' p,flyG P v p)=_
  rw [← quiverG.tsum_eq]; change (∑' p, (flyG P v ∘ quiverG) p)=_; rw [Summable.tsum_prod ((quiverG.summable_iff (f:=flyG P v)).2 (flyCost he hp v).of_abs)]
  change _= 2*(∑' i:Twig, ((Iteration.plain ∘ strata P) i).sample (flux (arm su n 1 x)) 0); rw [ht.tsum_sigma, ← tsum_mul_left]; refine tsum_congr fun i=> ?_; rw [tsum_fintype,tsum_fintype,Finset.mul_sum]; exact fieldR P x i
end YM.QCD.Smoke
