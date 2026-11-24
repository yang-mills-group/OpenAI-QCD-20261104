import YM.QCD.Smoke.Both

/-! # bake gradient again using ONLY column extent. costs stay uniform at input widths arbitrarily narrow relative to projection width. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lattice Wilson Finset Filter Function Metric Extra Iteration RG Placement Laurent Exterior Work.F08 Precision Bloch Matrix
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {L n c f : Side}{I:Type*}{η σ A C r:ℝ}{G:Gauge}{k:ℕ}

def taper (x:Cover):=route 0 x 1
lemma taper_size (x:Cover): (taper x).length=size x:=by rw [taper,route_length,sub_zero]
abbrev BridgeG:= (x:Cover) × Lift.Piece (taper x)
abbrev CompassG:= PlaqAxes × BridgeG
def alter (i:BridgeG):= Lift.floor 0 (taper i.1) i.2
def zephyr (i:BridgeG):= Lift.axis _ i.2
def cashG (i:BridgeG): ℝ:= Lift.sign _ i.2
lemma cashG_abs (i : BridgeG):|cashG i|=1:=by cases h: ((taper i.1)[i.2.val]'i.2.isLt).neg <;> simp [cashG,Lift.sign,h,List.get_eq_getElem]
lemma compassG (i:BridgeG): size (alter i)≤size i.1:=by have hx:=Lift.floor_size 0 (taper i.1) i.2; rw [show size (0:Cover)=0 from by simp [size],zero_add,taper_size] at hx; exact hx

def worthG (ψ:Columns L)(v : Pattern G k)(r:Site L) (p: CompassG) j:= entry ψ v r (fun _=> p.1) j p.2.1*cashG p.2
def endingG (r:Site L)(v:Pattern G k)(p:BridgeG) (j:Fin k):=carry r (v.atom.leg j).offset + alter p
def reasonG (ψ:Columns L) (v:Pattern G k)(r:Site L)(p:Fin k→CompassG):Pattern G k:=⟨fun i=> some (zephyr (p i).2),relocate v.atom (∏ i, worthG ψ v r (p i) i) (fun i=> endingG r v (p i).2 i) (fun j=> (p j).1)⟩
lemma reason_len (ψ:Columns L)(v : Pattern G k)(r:Site L)(p:Fin k→CompassG): (reasonG ψ v r p).atom.length≤ v.atom.length+8*k+∑ i,size (p i).2.1:=by
  have hL : 1 ≤ (L.val:ℝ):=by exact_mod_cast L.property
  have hh i: size (endingG r v (p i).2 i) ≤ (v.atom.leg i).length+4+size (p i).2.1:=by
    unfold endingG; apply (size_add ..).trans; refine Nat.add_le_add ?_ (compassG _)
    let x:=v.atom.leg i
    have hi : size x.offset ≤ x.length:= (offset_size x).trans (Nat.le_add_right ..)
    have hf: (↑(size (carry r x.offset)):ℝ)≤ ↑x.length+4:=by apply (carry_bound ..).trans; gcongr; apply le_trans (div_le_self (by positivity) hL); exact_mod_cast hi
    exact_mod_cast hf
  unfold reasonG; simp only [relocated_length]
  have ht:=sum_le_sum (s:=univ) (fun i _=>hh i); rw [sum_add_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at ht; simp only [Nat.cast_id] at ht; unfold Atom.length; omega -- check
variable {ψ : Columns L}
def passage (η:ℝ):= (Fintype.card PlaqAxes :ℝ)*momentPrice 1 (η/2)
lemma passage_pos (h:0<η):0 ≤ passage η:=mul_nonneg (by positivity) (momentPrice_pos _ (by positivity)).le
lemma cardsG (v:Pattern G k)(r:Site L)(j: Fin k)(hs: 0≤σ)(he: 0<η) (hk:σ≤η/2)(h:(ψ (v.op j)).strip η A): SumBudget (fun p:CompassG=> |worthG ψ v r p j| * Real.exp (σ*size p.2.1)) (passage η*A) :=by
  have hp (B:PlaqAxes): SumBudget (fun q:BridgeG=> |worthG ψ v r (B,q) j| * Real.exp (σ*size q.1)) (momentPrice 1 (η/2)*A):=by
    let s:=v.atom.leg j; let W:= entry ψ v r (fun _=> B) j
    let M:=momentPrice 1 (η/2)
    have hi: Laurent.Width η A W:=h (arrives r s.offset,plaquette s.plaq) (plaquette B)
    have ht : 0 ≤ M:= (momentPrice_pos _ (by positivity)).le
    refine Cost.sigma (Cost.scale hi M ht) (fun i:Cover=>?_) -- check F
    have hv (q:Lift.Piece (taper i)): |worthG ψ v r (B,⟨i,q⟩) j|=|W i|:=by unfold worthG; dsimp only; rw [abs_mul,cashG_abs,mul_one]
    simp only [hv]; apply Cost.enlarge (Cost.finite _ (by positivity))
    rw [Fintype.card_fin,taper_size]
    let n:ℝ:= size i; have hh:0 ≤ n:=by unfold n; positivity
    have he' : n≤M*Real.exp (η/2*n):= by have ht:= spendMoment 1 (show 0<η/2 by linarith) hh; unfold M; rw [pow_one] at ht; linarith
    apply (mul_le_mul_of_nonneg_right he' (by positivity : 0 ≤ |W i| *Real.exp (σ*size i))).trans; rw [Real.norm_eq_abs]
    calc
      _ = M*(Real.exp (η/2*n+σ*n)*|W i|):=by rw [Real.exp_add]; unfold n; ring
      _ ≤ _ :=by gcongr; unfold n at *; nlinarith
  have hx : 0 ≤ A := Cost.nonneg (h (r,plaquette (Classical.arbitrary _)) (plaquette (Classical.arbitrary _))) -- default?
  unfold passage; rw [mul_assoc]; exact Cost.product (Cost.finite (α:=PlaqAxes) (momentPrice _ _*A) (mul_nonneg (momentPrice_pos 1 (by positivity)).le hx)) hp

def cashRegister (k:ℕ)(η A:ℝ):=Real.exp (η*(8*k))*(passage η*A)^k
lemma muster (v:Pattern G k)(r:Site L)(hs:0 ≤ σ)(he:0<η)(hk:σ≤η/2)(h:∀ j,(ψ (v.op j)).strip η A): Charged (fun i=> (reasonG ψ v r i).atom) σ (cashRegister k η A*v.atom.budget σ):=by
  let Δ:=fun p:CompassG=> size p.2.1; have ht:=Cost.pi (fun i=> cardsG v r i hs he hk (h i)); simp only [prod_const,card_univ,Fintype.card_fin] at ht
  have hm : 0≤ v.atom.budget σ:=by unfold Atom.budget Atom.magnitude; positivity
  let d:=Real.exp (η*(8*k)); unfold cashRegister; rw [mul_right_comm]
  apply Cost.mono (Cost.scale ht (d*v.atom.budget σ) (mul_nonneg (Real.exp_pos _).le hm)) (fun i=> by unfold Atom.budget Atom.magnitude; positivity)
  intro i
  have hp := reason_len ψ v r i
  have hv : σ * (reasonG ψ v r i).atom.length≤ σ*v.atom.length +η*(8*k)+∑ j, σ*(Δ (i j):ℝ):=by
    refine (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hp) hs).trans ?_; push_cast; unfold Δ; rw [← mul_sum,mul_add,mul_add]; gcongr; linarith
  have hw : (reasonG ψ v r i).atom.magnitude= |∏ j,worthG ψ v r (i j) j| * v.atom.magnitude:= relocated_coeff ..
  unfold Atom.budget; rw [prod_mul_distrib,← Real.exp_sum, ← Finset.abs_prod]; apply (mul_le_mul_of_nonneg_left (Real.exp_monotone hv) (by unfold Atom.magnitude; positivity : 0 ≤ (reasonG ψ v r i).atom.magnitude)).trans_eq
  unfold d Δ; rw [hw,Real.exp_add,Real.exp_add]; ring
end YM.QCD.Smoke
