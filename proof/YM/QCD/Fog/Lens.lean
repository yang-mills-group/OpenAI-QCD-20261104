import YM.QCD.Fog.Reel

/-! # orbit footprint tally. receipt doesn't replace actual nonlinear action. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid YM.Next.Free
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical
variable {c n:Side}{I:Type}{G:Gauge}{r A:ℝ}
abbrev Rg (G:Gauge):= Atom G 2
abbrev View:= Fin 2→PlaqAxes
def viewG (A:Rg G)(t:Signed)(j:Fin 2):= PlaqAxes.rotate t (A.leg j).plaq
def planG (A:Rg G)(t:Signed)(j:Fin 2):= (Face.send t (0:Cover) ((A.leg j).offset,(A.leg j).plaq)).1
def marginG (A:Rg G)(t:Signed):=∏ j,turned t (A.leg j).plaq
def toll:ℝ:=(Fintype.card Signed:ℝ)⁻¹
lemma toll_on:0<toll:= inv_pos.mpr (by positivity)
def planish (A:Rg G)(t: Signed):Rg G:= relocate A (toll*marginG A t) (planG A t) (viewG A t)
lemma stencilG (A:Rg G)(t:Signed): (planish A t).length ≤ A.length+12:=by
  rw [planish,relocated_length,Atom.length]; have he (j:Fin 2) : Laurent.size (planG A t j)≤(A.leg j).length+2:= by
    have hx:= size_posG t (A.leg j).offset (A.leg j).plaq; exact hx.trans (by gcongr; exact (offset_size (A.leg j)).trans (Nat.le_add_right ..))
  have hp:=sum_le_sum (s:=univ) fun j _=>he j; rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hp; omega
lemma postsG (A:Rg G)(t:Signed): (planish A t).magnitude=toll*A.magnitude:=by rw [planish,relocated_coeff,abs_mul,abs_of_pos toll_on,marginG,Finset.abs_prod]; simp_rw [stamp_abs]; simp
lemma planished (A:Rg G)(h:0≤r): Charged (planish A) r (Real.exp (12*r)*A.budget r):=by
  have hv : 0≤toll:= toll_on.le
  have he:0 ≤ A.budget r:=by unfold Atom.budget Atom.magnitude; positivity
  refine Cost.enlarge (Cost.mono (Cost.finite (α:=Signed) (toll*(Real.exp (12*r)*A.budget r)) (by positivity)) (fun i=> by unfold Atom.budget Atom.magnitude; positivity) (fun i=>?_)) ?_
  · unfold Atom.budget; rw [postsG]; have hx : r *((planish A i).length:ℝ)≤ 12*r+r*A.length:= by
      apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (stencilG A i)) h).trans_eq; push_cast; ring
    apply (mul_le_mul_of_nonneg_left (Real.exp_monotone hx) (by unfold Atom.magnitude; positivity : 0 ≤ toll*A.magnitude)).trans_eq; rw [Real.exp_add]; ring
  rw [← mul_assoc,toll,mul_inv_cancel₀ (by positivity),one_mul]
def whiff (A:I→Rg G)(p:Signed× I):Rg G:= planish (A p.2) p.1
lemma whiff_sym {A:I→Rg G}(h:SymmetricAtoms A): SymmetricAtoms (whiff A):= fun j=>relocated_symm _ (h _) _ _ _
lemma whiff_budget {M:I→Rg G}(h:Charged M r A)(ht:0≤r): Charged (whiff M) r (Real.exp (12*r)*A):= by
  have he:=Cost.product (F:=fun p:I×Signed=> (planish (M p.1) p.2).budget r) (Cost.scale h _ (Real.exp_pos (12*r)).le) fun i => planished (M i) ht
  exact Cost.equiv (Equiv.prodComm Signed I) (f:=fun p:I×Signed=> (planish (M p.1) p.2).budget r) he
lemma heading (x y : Site n)(p:PlaqAxes)(s:Signed): (Face.send s (0:Site n) (x+y,p)).1=s.act x+(Face.send s (0:Site n) (y,p)).1:=by simp [Face.send, Face.lower,atFace,affine,Signed.act_add,add_assoc]
lemma windsG (x:Site n)(v:Dir G n)(p:PlaqAxes)(s:Signed)(i:G.ColorIndex): flux (pulled v s) p i x=turned s p*flux v (p.rotate s) i (Face.send s 0 (x,p)).1:=by
  have he:= rotations_d (parts G 1 v i) s x p; rw [← pigment] at he; exact he
lemma worn (A:Rg G)(s:Signed)(x:Dir G n)(y:Site n): (plain (planish A s)).sample (flux x) (s.act y)=toll*(plain A).sample (flux (pulled x s)) y:=by
  unfold Pattern.sample; simp only [plain,planish,relocate,slot_offset,slot_plaq,Iteration.read,Option.elim,mul_sum]; apply sum_congr rfl; intro i _; simp_rw [windsG, heading,send_wrap]; rw [prod_mul_distrib]; unfold viewG marginG planG; simp only [Prod.map_fst]; ring
lemma spins (M:I→Rg G)(h:Charged M r A)(ht:0 ≤r)(x:Dir G n): total (plain∘whiff M) (flux x)= Patch.average fun s:Signed=>total (plain∘M) (flux (pulled x s)):=by
  have he:= net_summable (plain∘whiff M) (flux x) ht (whiff_budget h ht)
  unfold total; rw [he.tsum_prod,tsum_fintype]; unfold Patch.average; rw [mul_sum]; apply sum_congr rfl; intro s _; rw [← tsum_mul_left]; apply tsum_congr; intro i
  rw [← Equiv.sum_comp (s.actEquiv (R:=Per n)).toEquiv]; rw [mul_sum]; apply sum_congr rfl; intro p _; exact worn ..
-- if calling action after normalizing, pull a second time, group action in linear logs
lemma down_pulled (x:Dir G n)(s t:Signed): Bid.pulled (Bid.pulled x s) t= Bid.pulled x (s*t):=by
  have he (r:ℝ): represent (r • pulled (pulled x s) t)=represent (r • pulled x (s*t)) :=by
    rw [← represent_pulled,← represent_pulled, pull_pull]; simp only [affine,Signed.act_zero,add_zero]; rw [represent_pulled]
  apply funext; rintro ⟨i,j⟩; obtain ⟨p,rfl⟩:=Exterior.axisEquiv.surjective j
  have hv := represent_rate (Bid.pulled (Bid.pulled x s) t) (i,p); simp_rw [he] at hv
  exact G.colorMat_injective (hv.unique (represent_rate (Bid.pulled x (s*t)) (i,p)))
lemma reels (x:Dir G n)(t:Signed)(A:I→Rg G): Patch.average (fun s:Signed=> total (plain∘ A) (flux (pulled (pulled x t) s)))= Patch.average fun s:Signed=> total (plain∘A) (flux (pulled x s)):=by
  unfold Patch.average; simp_rw [down_pulled]; have he := Equiv.sum_comp (Equiv.mulLeft t) (fun s=> total (plain ∘ A) (flux (pulled x s)))
  exact congr_arg _ he
end YM.QCD.Fog
