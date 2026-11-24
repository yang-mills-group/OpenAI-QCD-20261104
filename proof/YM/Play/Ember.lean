import YM.Play.Koi
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Many
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera.Oce
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly ProbabilityTheory ConnectedActivityE6.Poll
open scoped BigOperators Topology ContDiff Classical Matrix
variable {α:Type*}[MeasurableSpace α]{μ:Measure α}{A B:Type*}
-- Tilt law with shifted mean on the genuine regulator
variable (X₀:α→ℝ)(f k:ℝ)
local notation "F"=> mgf X₀ μ
variable (h:mgf X₀ μ = fun t:ℝ=> Real.exp (t*f+k*t^2/2))
include h
private lemma swerve (t:ℝ): HasDerivAt F ((F) t*(f+k*t)) t:=by
    have he:= ((((hasDerivAt_id' t).mul_const f).add ((((hasDerivAt_id' t).pow 2).const_mul k).div_const 2)).exp)
    rw [h]; convert! he using 1<;> simp <;> ring
private lemma stands (t:ℝ) : t∈ interior (integrableExpSet X₀ μ):=by
    have hv:integrableExpSet X₀ μ=Set.univ:=by
       ext x; refine ⟨fun _=>Set.mem_univ _,fun _=>?_⟩; by_contra hn; have ht:mgf X₀ μ x=0:=mgf_undef hn; rw [h] at ht; exact (Real.exp_pos _).ne' ht
    rw [hv,interior_univ]; exact Set.mem_univ _
lemma locus (n:ℕ): Integrable (fun x=> X₀ x^n) μ:= integrable_pow_of_mem_interior_integrableExpSet (stands _ _ _ h 0) n
lemma lead : (∫ x,X₀ x ∂μ)= f:=by
   rw [← deriv_mgf_zero (stands X₀ f k h _),(swerve X₀ f k h 0).deriv,h]; simp
private lemma derives (n:ℕ): iteratedDeriv (n+2) (F)= fun t=> k*(n+1)*iteratedDeriv n (F) t +(f+k*t)*iteratedDeriv (n+1) (F) t:=by
    have hv m t: HasDerivAt (iteratedDeriv m (F)) (iteratedDeriv (m+1) (F) t) t:= by rw [iteratedDeriv_mgf (stands _ _ _ h _)]; exact hasDerivAt_iteratedDeriv_mgf (stands _ _ _ h _) _
    have hf: deriv F=fun t=> F t*(f+k*t) := funext fun i=> (swerve _ _ _ h i).deriv
    induction n with
    | zero=>
       funext t; rw [show 0+2=1+1 by omega,iteratedDeriv_succ]
       rw [iteratedDeriv_one,hf]; have he := ((swerve _ _ _ h t).mul (((hasDerivAt_id' t).const_mul k).const_add f)).deriv
       rw [show deriv (fun i=> F i*(f+k*i)) t=_ from he]; simp; ring
    | succ n ih=>
       funext t; let g i:= iteratedDeriv i (F)
       have he:= (((hv n t).const_mul (k*(n+1))).add ((((hasDerivAt_id' t).const_mul k).const_add f).mul (hv (n+1) t))).deriv
       rw [show n+1+2=n+2+1 by omega, iteratedDeriv_succ, ih]; rw [show deriv (fun t:ℝ=> k*(n+1)*g n t +(f+k*t)*g (n+1) t) t=_ from he]; push_cast; rw [show n+1+1=n+2 by omega, ih]; ring -- body rewrite issue
lemma lends (n:ℕ): (∫ i,X₀ i^(n+2) ∂μ)= k*(n+1)* (∫ i,X₀ i^n ∂μ) + f*(∫ i,X₀ i^(n+1) ∂μ):=by
   have ht i: iteratedDeriv i F 0= _:= iteratedDeriv_mgf_zero (stands _ _ _ h _) i; simp_rw [Pi.pow_apply] at ht; rw [← show iteratedDeriv (n+2) F 0= _ from ht _, derives _ _ _ h]; dsimp only; rw [ht,ht]; simp
end YM.QCD.Bera.Oce
#print axioms YM.QCD.Bera.Oce.lends
