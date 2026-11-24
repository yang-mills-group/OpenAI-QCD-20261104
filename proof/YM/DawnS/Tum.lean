import YM.DawnS.Sap
import YM.Next.WARD_BIN.Degree

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis
open scoped Topology ContDiff
variable {r R:ℝ}(hr:0<r)(hR:0≤R)
--  h(t)=1/(r²+R t²). singular when R negative restrict. Eqn sum derivative.
def hLine (r R:ℝ)(t:ℝ):=1/(r^2+t^2*R)
def jLine(r R:ℝ)(t:ℝ):=(1/(r^2+t^2*R))^2
include hr
lemma hNice : ContDiffAt ℝ ∞ (hLine r R) 0:=ContDiffAt.div contDiffAt_const (contDiffAt_const.add ((contDiffAt_id.pow _).mul contDiffAt_const)) (show r^2 + (0:ℝ)^2 * R≠0 from by rw[zero_pow (by norm_num),zero_mul,add_zero]; positivity)
lemma jNice : ContDiffAt ℝ ∞ (jLine r R) 0:=(hNice hr).pow _ -- R captured by def?
#check iteratedDeriv_fun_mul
#check ENat.coe_lt_top
-- for any quadratic inverse,/?
lemma nearby : ∀ᶠ t in 𝓝 (0:ℝ), r^2+t^2*R≠0:=by apply (ContinuousAt.eventually_ne (x:=0) (show ContinuousAt (fun t:ℝ=>r^2+t^2*R) _ from by fun_prop)); change r^2+0^2*R≠0; rw[zero_pow (by norm_num),zero_mul,add_zero]; positivity
omit hr
lemma productD {f:ℝ→ℝ}(n:ℕ)(h:ContDiffAt ℝ ∞ f 0) : iteratedDeriv (n+2) (fun t:ℝ=>(r^2+t^2*R)*f t) 0 = r^2*iteratedDeriv (n+2) f 0 + ((n+2).choose 2)* (R*2)*iteratedDeriv n f 0:=by
     let g(t:ℝ):=t^2
     let k:=n+2
     have hx:ContDiffAt ℝ k f 0:= h.of_le (WithTop.coe_le_coe.mpr le_top) -- check
     have hp : iteratedDeriv k (fun t=>g t*f t) 0=(k.choose 2:ℝ)*2*iteratedDeriv n f 0:=by
          rw[iteratedDeriv_fun_mul (show ContDiffAt ℝ k g 0 from contDiffAt_id.pow 2) hx,Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by unfold k;omega))];
          · unfold g; rw[iteratedDeriv_fun_pow_zero]; norm_num [k] -- syntax choose smul
          intro i _ hi; unfold g; rw[iteratedDeriv_fun_pow_zero]; simp [hi]
     let z:=(fun t=> f t*r^2)+(fun t=> R*(g t*f t)) -- function auto 0 types
     rw [show (fun t=>(r^2+t^2*R)*f t)=z from funext fun t=>by unfold z; rw[Pi.add_apply]; unfold g; ring]; change iteratedDeriv k z _= _; unfold z; have hg : ContDiffAt ℝ k g 0:= contDiffAt_id.pow _; rw [iteratedDeriv_add (hx.mul contDiffAt_const) (contDiffAt_const.mul (hg.mul hx)),iteratedDeriv_const_mul_field, show (fun t=>f t*r^2)=(fun t=>r^2*f t) from funext fun x=>mul_comm ..,iteratedDeriv_const_mul_field]; change r^2*iteratedDeriv k _ _ + R*iteratedDeriv k _ _= _; rw[hp]; unfold k; ring
include hr
lemma hD (n:ℕ) : iteratedDeriv (2*n) (hLine r R) 0 = ((2*n).factorial:ℝ) / r^2 * (-R/(r^2))^n:=by
     induction n with
     | zero=> simp [hLine]
     | succ n ih=>
          let p:=2*n; have h: iteratedDeriv (p+2) (fun t:ℝ=>(r^2+t^2*R)*hLine r R t) 0=0:= by
               have h :(fun t:ℝ=>(r^2+t^2*R)*hLine r R t)=ᶠ[𝓝 0] (fun _=> 1):= (nearby (R:=R) hr).mono fun _ ht=>by unfold hLine; field_simp
               rw [(h.iteratedDeriv _).eq_of_nhds]; simp [iteratedDeriv_const] -- dummy
          rw[productD _ (hNice hr)] at h; rw [Nat.mul_succ]; change iteratedDeriv (p+2) _ 0=_
          rw[show iteratedDeriv p (hLine r R) 0=↑(p.factorial)/r^2*(-R/r^2)^n from ih] at h
          have hv:((p+2).factorial:ℝ)=((p+2).choose 2)*(2*(p.factorial:ℝ)):=by
                rw[← Nat.choose_mul_factorial_mul_factorial (show 2 ≤ p+2 by omega)]; simp; ring
          apply mul_left_cancel₀ (a:= r^2) (by positivity); apply Eq.trans (show r^2*_= -_ from eq_neg_of_add_eq_zero_left h) -- edit
          change -(_)=r^2*(((p+2).factorial:ℝ)/r^2 * (-R/r^2)^(n+1)); rw [hv,pow_succ (-R/r^2) n]; generalize (-R/r^2)^n=q; field_simp
lemma jD(n:ℕ): iteratedDeriv (2*n) (jLine r R) 0 = ((2*n).factorial:ℝ) * ((n+1:ℕ):ℝ) / r^4 *(-R/r^2)^n:=by
    induction n with
    | zero=>simp[jLine]; ring
    | succ n ih=>
         let f:= jLine r R; let p:=2*n; have h:(fun t:ℝ=>(r^2+t^2*R)*f t)=ᶠ[𝓝 0] hLine r R:=(nearby hr).mono fun _ ht=>by unfold f jLine hLine; field_simp
         have ht:=Eq.trans (productD (r:=r) (R:=R) p (show ContDiffAt ℝ ∞ f 0 from jNice hr)).symm ((h.iteratedDeriv _).eq_of_nhds)
         have hp:p+2=2*(n+1):=by unfold p; ring
         rw [show iteratedDeriv p f 0=_ from ih,hp,hD hr] at ht; change iteratedDeriv _ f 0=_
         apply mul_left_cancel₀ (a:=r^2) (by positivity); rw [show r^2 * _= _ from eq_sub_of_add_eq ht,← hp]
         have hv: ((p+2).factorial:ℝ)=(p+2).choose 2*(2*(p.factorial:ℝ)):=by rw[← Nat.choose_mul_factorial_mul_factorial (show 2 ≤ p+2 by omega)];simp;ring
         rw[hv,pow_succ (-R/r^2) n]; unfold p; generalize (-R/r^2)^n=q; push_cast; field_simp; ring
omit hr in
lemma dull(f:ℝ→ℝ)(hf:∀ x, f (-x)=f x)(m:ℕ) : iteratedDeriv (2*m+1) f 0=0:=by
     let j:=2*m+1; have hp: iteratedDeriv j f 0= - iteratedDeriv j f 0:=by nth_rw 1 [← funext hf]; rw [iteratedDeriv_comp_neg]; change (-1:ℝ)^j * _= _; rw[(show Odd j from ⟨m,rfl⟩).neg_pow]; simp
     linarith
end YM.DawnS
#print axioms YM.DawnS.hD
#print axioms YM.DawnS.jD
