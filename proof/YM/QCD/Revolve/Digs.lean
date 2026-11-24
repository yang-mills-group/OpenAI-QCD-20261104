import YM.QCD.Revolve.Bon

/-! # opposite endpoint in adjoint. Both gauges important even if output slice fixed. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 50000
namespace YM.QCD.Revolve
open Function Lattice Wilson Lat Kit Cost Run Rudder Finset RG Eyrie
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical
variable {n:Side}{s:Signed}{p:Spike}{g : Site n→ℂ}{k:ℕ}

def roll (x : Slot) (a : Walk):Slot:=⟨Lattice.reverse a++x.walk,x.plaq⟩
def clover (C : Bloom k): Bloom k:= ⟨Lattice.reverse C.tail,fun i=> roll (C.petals i) C.tail,fun i=> flag g5 (star (C.coeff i))⟩
lemma clove (C : Bloom k)(v):(clover C).hues v=flag g5 (star (C.hues v)):=by
  unfold flag Bloom.hues clover; rw [star_sum,Matrix.mul_sum,Matrix.sum_mul];apply sum_congr rfl; intro a _; rw [star_smul,Matrix.mul_smul,Matrix.smul_mul]; congr 2; simp
lemma clover_s (C: Bloom k)(h:C.Spins): (clover C).Spins :=by
  intro u v; rw [clove,clove,h,star_mul,star_mul,star_star, ← Matrix.mul_assoc (touch _),flag_gauge]
lemma g5_unit : g5∈unitary _:=⟨by simp,by simp⟩
lemma clover_le (C : Bloom k)(u:ℝ)(ht: 0 ≤ u): (clover C).paid u ≤ C.paid (u*(1+k)):=by
  have he: (clover C).span ≤ (1+k)*C.span:=by
    unfold Bloom.span clover Slot.length roll; dsimp only; simp only [List.length_append,Lattice.reverse,List.length_map,List.length_reverse]; simp only [add_assoc,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]; nlinarith [Nat.zero_le (∑ x:Fin k,(C.petals x).walk.length)]
  have ht': ((clover C).span:ℝ)≤(1+k)*C.span:=by exact_mod_cast he
  have hN : (clover C).price≤ C.price:= Finset.sum_le_sum (s:=univ) (fun i _=> (pays_five _ g5_unit (star (C.coeff i))).trans_eq (norm_star (C.coeff i)))
  apply mul_le_mul ?_ hN (Bloom.price_nn ..) (Real.exp_pos _).le
  apply Real.exp_monotone; nlinarith

lemma transit (x:Slot) (a : Walk)(U : Grid n)(y : Site n):
    (roll x a).atSite U (stop y a)= su.adjoint (travel U y a)⁻¹ (x.atSite U y):=by
  rw [Work.F03.atSite_path,Work.F03.atSite_path,roll]; dsimp only; rw [travel_append, travel_reverse,reverse_stop, Gauge.adjoint_mul]
  have hp : Work.F03.slotFace (roll x a) (stop y a)=Work.F03.slotFace x y:=Prod.ext (by
    unfold Work.F03.slotFace Slot.offset roll; dsimp only
    rw [add_comm,add_comm (wrap n _),← wrap_stop (stop y a), ← wrap_stop y, stop_append, reverse_stop]) rfl
  erw [show Work.F03.slotFace _ (stop y a)=_ from hp]

def newborn (n : Side)(A:Sheet n):=aura (chirality n) (star A)
lemma new_add (A B: Sheet n): newborn n (A+B)=newborn n A+newborn n B:=by rw [newborn,star_add,aura_add]; rfl
lemma new_smul (a:ℂ)(A:Sheet n): newborn n (a • A)=star a • newborn n A:=by rw [newborn,star_smul,aura_scale]; rfl
lemma new_id (A:Sheet n): newborn n (newborn n A)=A:=by
  let X:= chirality n
  have hu : star X*X=1:=by unfold X; rw [chi_star,chi_sq]
  unfold newborn aura; simp only [star_mul,star_star,chi_star, ← Matrix.mul_assoc,chi_sq,Matrix.one_mul]; rw [Matrix.mul_assoc,chi_sq,mul_one]
lemma clover_chi (C:Bloom k)(P:C.Spins)(t : Site n)(U:Grid n):
    (clover C).tonic t U=newborn n (C.tonic t U):=by
  let w:= C.tail; let h:Equiv.Perm (Site n):=Equiv.addRight (wrap n (stop (0:Cover) w))
  let J:= routeM t U w; let R:= fun x => winding x w t U
  have hJ: J=rides h R:= pinned ..
  let K:= chirality n; let A:= wave g5
  have hk : star K=K:= chi_star
  have hχ : K=rides (Equiv.refl _) fun _=>A:=rfl
  change rides (Equiv.refl _) _*routeM t U (Lattice.reverse w)=K*star (_*J)*star K
  rw [show K*star (_*J)*star K=_ from (rfl), flipping,hk,show routeM t U w=J from rfl,hJ,hχ]; simp only [star_mul,ride_ad,ride_mul]; congr 1
  funext i; let y:=h.symm i
  have hh x : h x=stop x w:=(wrap_stop ..).symm
  have hy : i=stop y w:=by rw [← hh,Equiv.apply_symm_apply]
  let B := travel U y w; let V := C.taste U y; let T:= touch (colour B)
  have hv: (clover C).taste U i=A*(star T*star V*T)*A:=by
    calc
      _ = flag g5 (star (C.hues fun k=> su.adjoint B⁻¹ ((C.petals k).atSite U y))) := by
        unfold Bloom.taste; rw [clove]; have hp i (x:Slot): (roll x w).atSite U i= (roll x w).atSite U i:=rfl
        have hm k : ((clover C).petals k).atSite U i=su.adjoint B⁻¹ ((C.petals k).atSite U y):=by rw [show i=stop y w from hy]; exact transit ..
        simp_rw [hm]
      _ = _ := by rw [P]; unfold flag T; simp only [colour_inv,touch_star,star_mul,star_star,wave_star,g5_star, Matrix.mul_assoc]; rfl -- touch_star simp orientation
  rw [show _=_ from hv]; change A*(star T*star V*T)*A*star (shimmer t y w • T)=A*(star (shimmer t y w • T)*star V)*A
  simp only [star_smul, Matrix.mul_smul,Matrix.smul_mul, Matrix.mul_assoc]; rw [← Matrix.mul_assoc T, show T*A = A*T from (interlace ..).eq,Matrix.mul_assoc A T,show T*star T=1 from (touch_u (x:=colour B) ⟨su.mat_star_mul _,su.mat_mul_star _⟩).2,mul_one]
end YM.QCD.Revolve
