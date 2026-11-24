import YM.QCD.Lunar.Ring
/-! # A global signal on exact torus, no choice of coordinates across parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
lemma neighL (i j:Site c)(he:Nonwrapping W o)(hi:i∈W)(hj:j∈W): lift (i-j) = lift (i-o)-lift (j-o):=by
   apply lift_eq_iff.mpr; refine ⟨?_,fun k=>?_⟩; · rw [map_sub,wrap_lift,wrap_lift]; abel
   have hp:(lift (i-o) k).natAbs ≤ separation i o:= component_le _ _
   have hl:(lift (j-o) k).natAbs ≤ separation j o:= component_le _ _
   have h:=he i hi; have hq:=he j hj; rw [Pi.sub_apply]; omega
noncomputable def cane (w:G.Color)(i:Axis)(x:Site c): Dir G c:= Pi.single (x,i) w
lemma linearization (A:G.Color)(o:Site c)(b:PlaqAxes): (wedge b A).field o=∑ i:Site c, (coord o i b.val.1) • (cane A b.val.2 i):=by
   ext1 ⟨i,j⟩; rw [wedge_field, Finset.sum_apply, Finset.sum_eq_single i]; rotate_left
   · intro k _ h; rw [Pi.smul_apply,show cane A b.val.2 k (i,j)=0 from (Pi.single_eq_of_ne (fun hh=> h (congr_arg Prod.fst hh.symm)) _),smul_zero]
   · simp
   rw [Pi.smul_apply]; by_cases he:b.val.2=j
   · change ite (b.val.2=j) _ _= _; rw [if_pos he,show cane _ _ _ _ = A from (he ▸ Pi.single_eq_same ..)]
   rw [if_neg he]; unfold cane; rw [Pi.single_eq_of_ne _ _,smul_zero]; intro hh; exact he (congr_arg Prod.snd hh.symm)
def detectorK (G:Gauge)(b:PlaqAxes)(A: Pot G c):ℝ := -(2:ℝ)⁻¹ * ∑ i:Site c,∑ j: Site c,(coord j i b.val.1)^2* logHessian A (cane (spike G) b.val.2 i) (cane (spike G) b.val.2 j)
-- canonical linear affine φ. Gauge.Invariant.B.C.Holm.
variable {A: Pot G c}(T:G.Simple)(B:P.Regular W A)
include T B
lemma inactiveP (g:G.Color)(i: Site c)(u: Dir G c)(hp:i∉W)(β:Axis): logHessian A (cane g β i) u=0:=by
    have hv: Agrees W (cane g β i) (0:Dir G c):=by intro e he hx; exact Pi.single_eq_of_ne (show e≠(i,β) from fun hh=>hp ((show e.1=i from congr_arg Prod.fst hh) ▸ he)) _
    rw [hessian_agrees T B hv (show Agrees W u u from fun _ _ _=>rfl), hessian_eq]; simp
lemma mean0 (g:G.Color)(u:Dir G c)(β:Axis)(he:Nonwrapping W o)(hc:4 ≤ c.val): ∑ i:Site c, logHessian A (cane g β i) u=0:=by
    let X : LinearJet G:=⟨Pi.single β g,fun _ _=>0⟩; let Y : LinearJet G:=⟨0,fun _ _=>0⟩
    have hV : X.field o=∑ i:Site c, cane g β i:=by ext1 ⟨i,j⟩; simp [LinearJet.field,cane, Finset.sum_apply,Pi.single_apply,X, ite_and]
    have he' : Y.field o=0:=by ext; simp [LinearJet.field,Y]
    have hh:=X.hessian_curl₁ T B he hc Y rfl u; rw [hV,he',hessian_eq,hessian_eq] at hh; rw [map_sum,_root_.sum_apply,map_zero] at hh; simpa only [hessian_eq,ContinuousLinearMap.zero_apply] using hh
lemma phase (b:PlaqAxes)(hc:4 ≤ c.val)(he:Nonwrapping W o): detectorK G b A= coeff A o b b:=by
    let I:=Site c; let X i:= coord o i b.val.1; let Y:= cane (spike G) b.val.2 (c:=c); let H(i j:I):=logHessian A (Y i) (Y j); unfold detectorK; change -(2:ℝ)⁻¹ * ∑ i:I,∑ j:I, (coord j i b.val.1)^2*H i j=_
    have hp (i j:I) : coord j i b.val.1 ^2 * H i j=(X i-X j)^2*H i j:=by
          by_cases hi:i∈W
          · by_cases hj:j∈W
            · unfold X coord; rw [neighL i j he hi hj, Pi.sub_apply,Int.cast_sub]
            rw [show H i j=0 from (hessian_symm B _ _).trans (inactiveP T B (spike G) j _ hj b.val.2),mul_zero,mul_zero] -- syntax
          rw [show H i j=0 from inactiveP T B (spike G) i _ hi b.val.2,mul_zero,mul_zero]
    have h1 : (∑ i:I,∑ j:I, X j^2*H i j)=0:=by rw [sum_comm]; simp_rw [← Finset.mul_sum,show ∀ j,∑ i:I,H i j=0 from fun j=>mean0 T B (spike G) (Y j) b.val.2 he hc,mul_zero,Finset.sum_const_zero]
    have h2 : (∑ i:I,∑ j:I, X i^2*H i j)=0:=by rw [sum_comm,← h1]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by rw [show H j i=H i j from hessian_symm B _ _]
    simp_rw [hp,show ∀ i j:I,(X i-X j)^2* H i j=X i^2*H i j+X j^2*H i j-2*(X i*(X j*H i j)) from fun i j=>by ring,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum (a:= (2:ℝ))];
    have hϕ : logHessian A ((wedge b (spike G)).field o) ((wedge b (spike G)).field o) = coeff A o b b:=rfl
    rw [h1,h2,←hϕ]; rw [linearization,hessian_eq,map_sum (fderiv ℝ (fderiv ℝ (germ A)) 0),_root_.sum_apply]; simp_rw [map_sum,map_smul,smul_apply,smul_eq_mul]
    rw [show -(2:ℝ)⁻¹ * _ = ∑ i:I,∑ j:I,X i * (X j*H i j) from ?_]; rotate_left; · ring
    unfold X H; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rw [hessian_eq]; ring
end YM.QCD.Lunar
