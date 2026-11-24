import YM.QCD.Pearl.Atom

/-!
# Momentum formula for paired charged test
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {n:Side}{I J D:Type}{p:Site n}{z:Momentum}{j : ℕ}{G:I→Gleam}{U:J→Bloom 1}{V:D→Bloom 2}{P:Plan j}{v:Train j}{η a b c:ℝ}(C : su.Color)
lemma packBill (h:Package η a b c P v G U V):billPack η a b c G U V:=⟨h.psi,h.first,h.second⟩
lemma path_nonzero (h:Package η a b c P v G U V)(n:Side):IsUnit (extent C G U V n 0).det:=by
  rw [dawn C h]
  let T:=links_inv v n; have he:= congr_arg Matrix.det T.2; rw [Matrix.det_mul,Matrix.det_one] at he
  exact IsUnit.mk0 _ (fun e=>zero_ne_one (α:=ℂ) (by rw [← he,e,zero_mul]))
def simp_k (v:Train j)(k:Momentum):= (Para.model (Dir v k))⁻¹
def drop (v:Train j)(k:Momentum):= Para.model (Para.reciprocalP (Dir v k))
lemma slip (v : Train j){k:Momentum}(h:k∈realCube zone)(hk:k≠0):simp_k v k=drop v k:=by unfold simp_k drop; rw [Para.live_inv (nonzeroD h hk)]
lemma plac (v:Train j)(k:Site n): rangeG v k=drop v (tuning k):=by unfold rangeG; rw [full_match (dog k) (tune_nonzero k)]; exact slip _ (dog k) (tune_nonzero k)
lemma skyl {M:Sheet n}: (peel M).trace=M.trace:=by unfold peel; rw [Matrix.trace_mul_cycle, (leaf_u _).2,one_mul]
lemma line_tr (G:Site n→Bundle): (lined G).trace=∑ k, (G k).trace:= by
  unfold Matrix.trace Matrix.diag lined; rw [Fintype.sum_prod_type]; simp_rw [rides, Equiv.refl_apply,Matrix.of_apply,if_true]
lemma balustrade (pum p:Momentum)(he: ∀ i: Axis, mode pum (step i)=mode p (step i)):
    ∃ v:Cover,pum=p+Laurent.reciprocal v:=by
  have ht (i : Axis): ∃ v:ℤ,pum i=p i+(v:ℂ)*(2*Real.pi):=by
    have hh:= he i; rw [Exterior.factor,Exterior.factor] at hh
    rw [Complex.exp_eq_exp_iff_exists_int] at hh -- check
    obtain ⟨v,hv⟩:=hh; refine ⟨v,?_⟩; apply mul_left_cancel₀ Complex.I_ne_zero; linear_combination hv
  choose v hv using ht
  refine ⟨v,funext fun i=>?_⟩; rw [hv i]; simp only [Laurent.reciprocal,Pi.add_apply]; ring
lemma fan_shift (k:Site n) (h: Fans p z):∃ v:Cover,tuning (k+p) = (tuning k + z) + Laurent.reciprocal v:=by
  apply balustrade
  intro i; rw [mode_phase,h (step i),shiftPhase (k+p),shiftPhase k,mode_phase,mode_phase,← cell_wrap (k+p),cell_duality (k+p),cell_add,← cell_duality k, ← cell_duality p,cell_wrap]; -- inspect
  simp_rw [wrap_step]; ring
lemma tinct (k:Site n) (h: Fans p z) (hp:tuning k+z∈realCube zone): drop v (tuning k+z)=drop v (tuning (k+p)):=by
  obtain ⟨u,hu⟩:=fan_shift k h; unfold drop; rw [hu, period_dir _ _ hp (by rw [← hu]; exact dog _)]
lemma signal_eq (i:Axis){y k: Momentum}{u:Cover}: v₁ G U C i (y,k+Laurent.reciprocal u)=v₁ G U C i (y,k):=by simp [v₁,boom₁,nil₁,boom,wane]

def furniture (A B:Shine→Bundle) (v:Train j)(z k:Momentum):=
    (drop v k * A (-z,k+z)*drop v (k+z)* A (z,k)).trace - (drop v k* B (z,k)).trace
def polarization (M:Weather n→Sheet n)(i:Axis) (p : Site n):= -(dig (flashT p i) (flashT (-p) i) (actual M) 0)
lemma path_price (h:Package η a b c P v G U V)(i:Axis) (he: Fans p z) (hp:∀ k : Site n,tuning k+z ∈realCube zone):
    polarization (extent C G U V n) i p=∑ k:Site n,furniture (v₁ G U C i) (v₂ G U V C i) v z (tuning k):=by
  let M:= extent C G U V n
  let A:= v₁ G U C i; let B:= v₂ G U V C i
  let q:= flashT p i; let u:=flashT (-p) i
  have ht:= hilt C (packBill h) h.scale he i; change peel _=_∧peel _=_ at ht
  have hy:= (hilt C (packBill h) h.scale he.negative i).1
  have hx : (M 0)⁻¹=stage v n:= (congr_arg Inv.inv (dawn C h n)).trans (stage_eq v n).symm
  let X:Sheet n:=(M 0)⁻¹; let D:= dew q M 0; let W:=dew u M 0; let Y:=dig q u M 0
  have hz : (X*D*X*W).trace-(X*Y).trace=polarization M i p:=by unfold polarization; rw [dig_actual (aria C (packBill h) h.scale n) (path_nonzero C h n), neg_sub]
  change polarization M i p = _; rw [← hz, show X=stage v n from hx];
  let T:= stage v n
  have heX: peel (T*D)=cloud p fun k=>rangeG v (k+p)*A (z,tuning k):=by rw [peel_mul,show peel T=lined _ from carries _, show peel D=_ from ht.1, side_cloud]
  have heW : peel (T*W)=cloud (-p) fun k=>rangeG v (k+ -p)* A (-z,tuning k):=by rw [peel_mul,show peel T=lined _ from carries _,show peel W=_ from hy,side_cloud]
  change _-_=_; rw [show (stage v n * D * _ * W).trace=(peel (T*W)*peel (T*D)).trace from ?_,show (stage v n * Y).trace=(lined (fun k=> rangeG v k* B (z,tuning k))).trace from ?_, heX, heW, cloud_dawn,line_tr,line_tr,← sum_sub_distrib]
  · apply sum_congr rfl; intro k _; simp only [add_neg_cancel_right]; unfold furniture; rw [plac,plac,tinct k he (hp k)]; unfold A B; have hh : v₁ G U C i (-z,tuning (k+p))=v₁ G U C i (-z,tuning k + z):=by obtain ⟨u,h'⟩:=fan_shift k he; rw [h']; exact signal_eq C _
    rw [hh]; simp only [mul_assoc]
  · rw [← skyl (M:=stage v n*Y),peel_mul, show peel (stage v n)=_ from carries _,show peel Y= _ from ht.2,lined_law]; rfl
  rw [← peel_mul,skyl,mul_assoc (stage v n* D), Matrix.trace_mul_comm]
end YM.QCD.Pearl
