import YM.QCD.Fog.Silk

/-! # the accepted quadratic score array. alpha taken on coarse bed metric before charged scores -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid YM.Next.Free Placement Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable (T:Bed) {r A:ℝ}{n:Side}
abbrev Ledger:= PlaqAxes × PlaqAxes × Cover
def rateG (p:Ledger):ℝ:=T.metric (plaquette p.1) (plaquette p.2.1) p.2.2
def boot (p:Ledger) :Rg su:= {leg:=![slot 0 p.1,slot p.2.2 p.2.1], coeff:= fun x:Cink=> rateG T p / 2 * inkMark x }
lemma boot_poly (p:Ledger)(x:Fin 2→su.Color): (boot T p).poly x=rateG T p/2 * ⟪x 0,x 1⟫_ℝ:=by
  unfold boot Atom.poly; rw [Work.F03.inner_color (G:=su),mul_sum]
  let v:= Fin.consEquiv (n:=1) (fun _:Fin 2=> su.ColorIndex)
  rw [← Equiv.sum_comp v]; rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=> ?_
  rw [sum_eq_single (fun _ :Fin 1=> i)]
  · unfold inkMark; rw [Fin.prod_univ_two]; change _* (if i=i then (1:ℝ) else 0)*_= _; rw [if_pos rfl,mul_one]; rfl
  · intro y _ h; have hh:i ≠ y 0:= fun e=> h (funext fun j=> by fin_cases j; exact e.symm)
    unfold inkMark; dsimp only; erw [show (v (i,y)) 0=i from rfl, show (v (i,y)) 1=y 0 from rfl,if_neg hh,mul_zero,zero_mul]
  simp
lemma boots : SymmetricAtoms (boot T):=by
  intro i v y; simp only [boot_poly]; congr 1; exact (LinearIsometry.inner_map_map (⟨su.adjoint v,su.norm_adjoint v⟩ : su.Color →ₗᵢ[ℝ] su.Color)) _ _
lemma boot_magnitude (p:Ledger): (boot T p).magnitude ≤ |rateG T p| * Fintype.card Cink:=by
  have hp i: |(boot T p).coeff i| ≤ |rateG T p|:=by unfold boot; dsimp only; rw [abs_mul]; apply (mul_le_of_le_one_right (abs_nonneg _) _).trans; rw [abs_div]; norm_num;  unfold inkMark; split <;> simp
  unfold Atom.magnitude; apply (sum_le_sum (s:=univ) fun i _=> hp i).trans; rw [sum_const,card_univ,nsmul_eq_mul,mul_comm]
def bootPrice (r A:ℝ):= (Fintype.card PlaqAxes:ℝ)^2*(Real.exp (8*r)*(Fintype.card Cink)*A)
lemma bootPOS (r:ℝ){A:ℝ}(h:0≤A):0≤bootPrice r A:=by unfold bootPrice; positivity
lemma bootLeg (hp:T.metric.strip r A)(p q:PlaqAxes): Charged (fun i=>boot T (p,q,i)) r (Real.exp (8*r)*(Fintype.card Cink)*A):=by
  apply Cost.mono (Cost.scale (hp (plaquette p) (plaquette q)) (Real.exp (8*r)*(Fintype.card Cink)) (by positivity)) (fun i=>by unfold Atom.budget Atom.magnitude; positivity) fun i=>?_
  unfold Atom.budget; apply (mul_le_mul_of_nonneg_right (boot_magnitude T (p,q,i)) (Real.exp_pos _).le).trans_eq; rw [show ((boot T (p,q,i)).length:ℝ)=8+ size i from ?_,mul_add, Real.exp_add,Real.norm_eq_abs, mul_comm r 8]; unfold rateG; ring
  simp [boot, Atom.length, Laurent.size]; ring
lemma bootBill (hp:T.metric.strip r A): Charged (boot T) r (bootPrice r A):=by
  let d :ℝ:= Fintype.card PlaqAxes
  let X:= Real.exp (8*r)*(Fintype.card Cink)*A
  have hh : 0≤A:= Cost.nonneg (hp (plaquette (Classical.arbitrary _)) (plaquette (Classical.arbitrary _)))
  have hx:0≤X:=by unfold X; positivity
  have hp'p (p:PlaqAxes):Charged (fun i=> boot T (p,i)) r (d*X):=Cost.product (Cost.finite _ hx) fun q=>bootLeg T hp p q
  unfold bootPrice; rw [pow_two,mul_assoc]; exact Cost.product (Cost.finite (α:=PlaqAxes) _ (mul_nonneg (by positivity) hx)) hp'p
lemma boot_charge (p q : PlaqAxes)(x:Cover): sharesG (boot T (p,q,x))= if p=q then (rateG T (p,q,x)/2)/(Fintype.card PlaqAxes:ℝ) else 0 :=by
  unfold sharesG propertyG charge
  by_cases h:p=q <;> rw [sum_eq_single p]
  · subst q
    rw [if_pos rfl, if_pos (show (fun i=> ((boot T (p,p,x)).leg i).plaq) = (fun _=> p) from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩))]; unfold boot inkMark; simp only [if_true,mul_one]
  · intro i _ hv; rw [if_neg]; intro ht; exact hv (congr_fun ht 0).symm
  · simp
  · rw [if_neg h, if_neg, zero_div]; intro he; exact h (congr_fun he 1).symm
  · intro i _ he; rw [if_neg]; intro hm; exact he (congr_fun hm 0).symm
  simp
lemma boot_normal (hp:T.metric.strip r A)(hr:0<r)(h:T.metric.read 0=1):depositG (boot T)=1/2:=by
  have H:=sharesSum (boot T) (bootBill T hp) hr; unfold depositG; rw [H.tsum_prod,tsum_fintype]
  simp_rw [(H.prod_factor _).tsum_prod,tsum_fintype,boot_charge]; let C:ℝ:= Fintype.card PlaqAxes
  have hC:0<C:=by unfold C; positivity
  have hs p : (∑ q:PlaqAxes,∑' x:Cover,(if p=q then rateG T (p,q,x)/2/C else 0))=1/2/C:=by
    rw [sum_eq_single p]
    · simp only [if_true, tsum_div_const]; unfold rateG; have ht:= congr_arg (fun M:Matrix (TypeFace 2) (TypeFace 2) ℂ=> M (plaquette p) (plaquette p)) h; simp only [Bloch.Row.read,Laurent.read,Matrix.of_apply,mode_constant, one_smul, Matrix.one_apply_eq] at ht; -- inspect
      congr 2; apply Complex.ofReal_injective; rw [Complex.ofReal_one,Complex.ofReal_tsum]; exact ht
    · intro b _ hb; simp [hb.symm]
    simp
  rw [sum_congr rfl fun i _=> hs i,sum_const,nsmul_eq_mul,card_univ]; change C * _= _; field_simp -- inspect
end YM.QCD.Fog
