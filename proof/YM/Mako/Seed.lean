import YM.Work.A13
import YM.MassiveTwoEstimates.SpinGeometry
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Analysis Lattice
open Massive MassiveTwoEstimates MassiveTwoEstimates.SpinGeometry
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
noncomputable abbrev oathU (g:Ortho.Skew):ℝ→EuPin:= (geometry.path g).choose
lemma tour(g:Ortho.Skew): EuPin.Path g (oathU g):=(geometry.path g).choose_spec
noncomputable abbrev euca:EuPin →* Ortho:= ⟨⟨EuPin.coord,rfl⟩,fun _ _=>rfl⟩ -- syntax?
lemma curve_i {g:Ortho.Skew}{f:ℝ→EuPin}(h:EuPin.Path g f)(r:ℝ):f (-r)=(f r)⁻¹:=by
     apply eq_inv_of_mul_eq_one_left; rw[← SpinParity.additive h]; simp [h.1]
-- generate by arbitrary skew lifts (later need just planes)
lemma engenders(H:Subgroup EuPin)(h:∀ (p:EuPin)(s:Signed),p.Lifts s→ p∈H)(hV:∀ g:Ortho.Skew,∀ t:ℝ,oathU g t∈ H)(x:EuPin):x∈H:=by
    have ht :⊤ ≤H.map euca:=by
         rw[← show Bid.AxisGens=⊤ from Work.A13.answer]
         refine (Subgroup.closure_le _).mpr ?_
         rintro p (⟨s,rfl⟩|⟨g,t,rfl⟩); · obtain ⟨q,hq⟩:=geometry.euclidean _; exact Subgroup.mem_map.mpr ⟨q,h _ s hq,hq⟩
         exact Subgroup.mem_map.mpr ⟨_,hV g t,(tour g).2.2 t⟩
    obtain ⟨p,hp,he⟩:= Subgroup.mem_map.mp (ht (Subgroup.mem_top x.coord))
    have hx: EuPin.Lifts (x*p⁻¹) 1:=by change euca (x*p⁻¹) = Signed.inclusionO 1; rw [map_mul,map_inv,map_one,he]; exact mul_inv_cancel _
    have hy:=H.mul_mem (h _ _ hx) hp; rwa [mul_assoc,inv_mul_cancel,mul_one] at hy
-- ODE uniqueness
lemma reaps {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V](L:V →L[ℝ] V)
     (f:ℝ→V)(h:∀x, HasDerivAt f (L (f x)) x)(r:ℝ): f r=NormedSpace.exp (r • L) (f 0):=by
     let P(t:ℝ):=NormedSpace.exp (t • L); have hf(u:ℝ) : HasDerivAt (fun t:ℝ=> P (-t) (f t)) 0 u:=by
            have he:= hasDerivAt_exp_smul_const L (-u); change HasDerivAt P _ _ at he
            have ha:HasDerivAt (fun t:ℝ=> -t) (-1) u:= (hasDerivAt_id u).neg; have hi:= (he.scomp u ha).clm_apply (h u); refine hi.congr_deriv ?_; rw [neg_one_smul]; exact neg_add_cancel _
     have hr : P (-r) (f r)= P (-0) (f 0):= is_const_of_deriv_eq_zero (fun x=>(hf x).differentiableAt) (fun x=>(hf x).deriv) r 0
     have hm : P r * P (-r)=1:=by
            letI : NormedAlgebra ℚ (V →L[ℝ] V):=.restrictScalars ℚ ℝ _; unfold P; rw[neg_smul,← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl (r • L))), add_neg_cancel]; simp
     have hP : P (-r) (f r)=f 0:=by rw [hr]; simp[P]
     rw[← hP]; show f r=(P r * P (-r)) (f r); rw [hm]; rfl
end YM.Mako
#print axioms YM.Mako.engenders
#print axioms YM.Mako.reaps
