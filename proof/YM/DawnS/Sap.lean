import YM.DawnS.Polar
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Set Filter MeasureTheory Lattice Function
open scoped Classical BigOperators InnerProductSpace ContDiff Pointwise Topology ENNReal
local notation "Y" => Vertex
local notation "P"=> RingS
local notation "e" => base 0
noncomputable def thetaS (v:Y)(x:P):ℝ:= inner ℝ v x.val
lemma ray (i:Fin 3)(x:P): thetaS (base i) x = (x.val) i:= (EuclideanSpace.basisFun ..).repr_apply_apply .. |>.symm.trans (by simp)
noncomputable def eta (a b:Y)(n m:ℕ):ℝ:=∫ y:P, (thetaS a y)^n*(thetaS b y)^m ∂muS
lemma hInt (a b:Y)(n m:ℕ): Integrable (fun y:P=>thetaS a y^n*thetaS b y^m) muS:=((show Continuous _ by unfold thetaS; fun_prop)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma gitt (a b:Y)(n:ℕ)(t:ℝ): surf n (a+t • b)=∑ i∈Finset.range (n+1), ((n.choose i:ℕ):ℝ)*eta b a i (n-i)*t^i:=by
     unfold surf; have hx(y:P) : inner ℝ (a+t • b) y.val ^ n =∑ i∈Finset.range (n+1), (((n.choose i:ℕ):ℝ)*t^i)*(thetaS b y^i*thetaS a y^(n-i)):=by rw [add_comm a,inner_add_left,real_inner_smul_left,add_pow]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [mul_pow]; unfold thetaS; ring
     simp_rw[hx]; rw[integral_finsetSum]; swap
     · exact fun i _=> (hInt b a i _).const_mul _
     exact Finset.sum_congr rfl fun i _=> by rw [integral_const_mul]; unfold eta; ring
lemma traceAxis (b:Y)(m:ℕ)(h:‖b‖=1)(hx: inner ℝ b e=0): eta b e 2 (2*m)*(2*m+1:ℝ)=surf (2*m+2) e:=by
     let n:=2*(m+1); have he(t:ℝ):‖e + t • b‖^n=(1+t^2)^(m+1):=by unfold n; rw [pow_mul,norm_add_sq_real]; rw [inner_smul_right,real_inner_comm, hx,norm_smul,h]; simp
     let F(t:ℝ):=surf n (e + t • b); have hF(t:ℝ): F t=(∑ i∈Finset.range (m+1+1), ((((m+1).choose i:ℕ):ℝ)*surf n e)* t^(2*i)):=by
           unfold F; rw [sphereNorm _ _,he t,add_comm (1:ℝ),add_pow,Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=>?_ ; simp only [one_pow,mul_one]; rw [pow_mul]; ring
     let a(i:ℕ):ℝ:=n.choose i*eta b e i (n-i)
     let f(t:ℝ):=∑ i∈ Finset.range (n+1), a i*t^i; have h0:F=f:=funext fun t=>gitt _ _ n t
     let g:= iteratedDeriv 2 F 0
     have h₁:g=a 2 * 2 :=by
           unfold g; rw [h0, show iteratedDeriv 2 f 0= _ from iteratedDeriv_fun_sum (f:=fun i t=> a i*t^i) (fun i _=> (contDiffAt_const.mul (contDiffAt_id.pow i)))]; -- check syntax signature f/index
           rw [Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by unfold n; omega))]
           · rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero]; norm_num
           intro i _ hi; rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero]; simp [hi,Ne.symm hi]
     have h₂:g=(((m+1).choose 1:ℕ):ℝ)*surf n e *2:=by
           unfold g; rw [funext hF, iteratedDeriv_fun_sum (fun i _=> contDiffAt_const.mul (contDiffAt_id.pow (2*i))), Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega))];
           · rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero]; norm_num
           intro i _ hi; rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero]; have h:2 * i ≠ 2:=(by omega)
           simp [h,Ne.symm h]
     have he':a 2=(n.choose 2:ℝ)*eta b e 2 (2*m):=by unfold a n; congr 2
     have hY:((n.choose 2:ℝ))*2=n*((n:ℝ)-1):=by
          have hn:1≤n:=by unfold n; omega
          have hv : n.choose 2 * 2=n*(n-1):=by rw[Nat.choose_two_right,Nat.div_mul_cancel]; exact dvd_mul_of_dvd_left ⟨m+1,rfl⟩ _
          have he:=congr_arg (fun x:ℕ=>(x:ℝ)) hv; push_cast [hn] at he; exact he
     rw [he'] at h₁; rw [Nat.choose_one_right,Nat.cast_add,Nat.cast_one] at h₂
     have h:n=2*m+2:=by unfold n; omega
     rw[h] at h₁ h₂ hY; push_cast at hY
     have hz:= congr_arg (· * eta b e 2 (2*m)) hY; apply mul_left_cancel₀ (a:=2*(m:ℝ)+2) (by positivity); linarith only [h₁,h₂,hz]
-- additional
noncomputable abbrev sky := surf 0 e
lemma sky_pos : 0<sky:=by simp only [sky,surf,pow_zero,integral_const]; rw [smul_eq_mul,mul_one]; exact ENNReal.toReal_pos (Ne.symm (ne_of_lt (IsOpen.measure_pos muS isOpen_univ Set.univ_nonempty))) (measure_ne_top _ _) -- name
lemma transmit (m:ℕ): surf (2*m+2) e*(2*m+3:ℝ)=surf (2*m) e*(2*m+1:ℝ):=by
     have h(i:Fin 3) := traceAxis (base i) m (hue i)
     let f (i:Fin 3)(y:P):=thetaS (base i) y^2 * thetaS e y^(2*m)
     have hh(y:P): inner ℝ e y.val ^ (2*m) = ∑ i:Fin 3,f i y:=by unfold f; rw[←Finset.sum_mul]; simp_rw [ray]; rw[← EuclideanSpace.real_norm_sq_eq,y.property |> mem_sphere_zero_iff_norm.mp]; simp only [one_pow,one_mul]; rw [show inner ℝ e y.val=_ from ray 0 y]
     have ht: eta e e 2 (2*m) =surf (2*m+2) e:=by unfold eta surf thetaS; simp only[pow_add, mul_comm ((inner ..)^2)] -- lemma
     have h':surf (2*m) e=∑ i:Fin 3,eta (base i) e 2 (2*m):=by unfold surf; simp_rw[hh]; exact integral_finsetSum _ fun i _=> hInt ..
     have hx : inner ℝ (base 1) e=0 := by simp [base,EuclideanSpace.inner_eq_star_dotProduct];
     have hz : inner ℝ (base 2) e=0 := by simp [base,EuclideanSpace.inner_eq_star_dotProduct];
     rw[h',Fin.sum_univ_three, add_mul, add_mul,h 1 hx,h 2 hz,ht]; ring
lemma evolved (m:ℕ)(v:Y) : surf (2*m) v * (2*m+1:ℝ)= ‖v‖^(2*m)*sky:=by
     rw [sphereNorm, mul_assoc]
     apply congr_arg (‖v‖^(2*m) * ·)
     induction m with| zero=> norm_num; rfl | succ m ih=> push_cast; rw[Nat.mul_succ,show (2*((m:ℝ)+1)+1:ℝ)=2*m+3 from by ring,transmit]; exact ih
end YM.DawnS
#print axioms YM.DawnS.evolved
