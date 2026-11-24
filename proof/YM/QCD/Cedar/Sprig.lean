import YM.QCD.Cedar.Park

/-!
# exact Wilson connection, top
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pine
open Lat Cost Lattice Wilson Function Finset Flume
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Matrix.Norms.L2Operator Topology BigOperators Matrix Kronecker
variable {n : Side} {j : ℕ} (P : Plan j) (t : Site n)
lemma top_tile (U : Grid n) (a : Axis): walls P t (.top j) U a=(2:ℂ)⁻¹ • leaves (arcL t U a):=by
  have hh : deck t U (P.Herm (.top j) a)=(Real.sqrt (1/2-P.μ):ℂ) • 1:=by
    unfold deck; rw [tsum_eq_single 0]; simp only [mote_nil]; unfold Plan.Herm; rw [if_pos (show Plan.flatPeak (.top j) from rfl)]; simp [Plan.clove,token]
    intro i hi; unfold Plan.Herm; rw [if_pos (show Plan.flatPeak (.top j) from rfl)]; simp [Plan.clove,token,hi]
  have hs : ((Real.sqrt (1/2-P.μ):ℂ))*(Real.sqrt (1/2-P.μ):ℂ)=(1:ℂ)/2-(P.μ:ℂ):=by rw [← Complex.ofReal_mul,Real.mul_self_sqrt (sub_nonneg.mpr P.below.le)]; push_cast; rfl
  let z := arcL t U a
  have hx (X : Sheet n): leaves ((Real.sqrt (1/2-P.μ):ℂ) • (1:Sheet n)*X)=(1/2-(P.μ:ℂ)) • leaves X:=by
    unfold leaves; rw [Matrix.smul_mul,one_mul,star_smul, Matrix.smul_mul, Matrix.mul_smul,smul_smul]; simp only [Complex.star_def,Complex.conj_ofReal,hs]
  unfold walls; rw [hh]; dsimp only; rw [hx,hx,lawful]; unfold half; rw [← two_smul ℂ _, smul_smul,inv_mul_cancel₀ (by norm_num),one_smul,← add_smul]; congr 1; ring
lemma oneWalk (a : Step) (o): route 0 a.vec o=[a]:=by
  have he (l : List Axis) (h:l.Nodup): axisRoute 0 a.vec l= if a.dir∈l then [a] else []:=by
    induction l with
    | nil=> simp [axisRoute]
    | cons i l ih=>
      rw [show axisRoute 0 _ (i::l)=straight i (a.vec (R:=ℤ) i-0)++axisRoute 0 _ l from rfl, ih (List.nodup_cons.mp h).2]
      by_cases ht : i=a.dir
      · subst i; have hh:= (List.nodup_cons.mp h).1
        cases a with | mk j b=> cases b <;> simp_all [straight,Step.vec]
      have hm : a.vec (R:=ℤ) i=0:=by unfold Step.vec; split <;> simp [ht]
      rw [hm]; simp [straight,Ne.symm ht]
  unfold route allAxes; rw [he _ ((List.nodup_finRange _).map o.injective), if_pos (List.mem_map.mpr ⟨o.symm a.dir,by simp, by simp⟩)]
lemma first_mote (U : Grid n) (a : Step) : mote t U a.vec= leg t U a:=by
  unfold mote; simp_rw [oneWalk, routeM,List.map_singleton,List.prod_singleton, sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ votes_ne,one_smul]
lemma hourC (U : Grid n) (hj : 2≤j) (a : Axis): deck t U (alphaT (.top j) a)=(2:ℂ)⁻¹ • (shift t U a-star (shift t U a)) := by
  let u:Cover:=step a; have ht : u≠-u:=by intro h; replace h:=congr_fun h a; simp [u] at h
  unfold deck; rw [tsum_eq_sum (s:={u,-u})]
  · rw [sum_pair ht]; simp_rw [orth_coeff hj,token]
    rw [show mote t U u=shift t U a from first_mote t U (posDir a), show mote t U (-u)=star (shift t U a) from first_mote t U (negDir a)]; simp [div_eq_mul_inv,sub_eq_add_neg,u,show step a ≠ -(step a:Cover) from ht,show -(step a:Cover) ≠ step a from ht.symm]
  intro i hi; rw [mem_insert,mem_singleton,not_or] at hi; rw [orth_coeff hj]; simp [token,show i≠step a from hi.1,show i≠ -step a from hi.2]
lemma lows (a : Axis): onSpin n (lo a)=(2:ℂ)⁻¹ • (1-onSpin n (gamma a)) ∧ onSpin n (hi a)=(2:ℂ)⁻¹ • (1+onSpin n (gamma a)):=by
  have he (X : Spike) (k : ℂ): onSpin n (k • X)=k • onSpin n X:=by unfold onSpin wave; rw [ride_smul, Matrix.smul_kronecker]; rfl
  rw [lo,hi,he,he,← on_spin_add,on_spin_one]; refine ⟨?_,rfl⟩; congr 1; rw [eq_sub_iff_add_eq,on_spin_add,sub_add_cancel,on_spin_one]
lemma w_branch (v : Plan j) (U : Grid n) (a : Axis) : walls v t (.top j) U a + skewL (vein t (.top j) a U) = 1-singleHop t U a:=by
  rw [top_tile,vein,hourC _ _ v.good]
  let F:=shift t U a; let P:=onSpin n (gamma a)
  have hu:star F*F=1:=(shift_u ..).1
  have hs:star P=P:=by unfold P; rw [on_spin_star,gamma_star]
  have he : star (P*((2:ℂ)⁻¹ • (F-star F)))= -(P*((2:ℂ)⁻¹ • (F-star F))) :=by
    rw [star_mul,hs,star_smul,star_sub,star_star, show star ((2:ℂ)⁻¹)=_ from (by simp : star ((2:ℂ)⁻¹)=(2:ℂ)⁻¹)]
    rw [Matrix.smul_mul,Matrix.mul_smul,mul_sub,sub_mul,(shift_spin ..).eq,(back_spin ..).eq,← neg_sub (P*F),smul_neg] -- sign
  unfold leaves arcL singleHop skewL; rw [he]
  rw [sub_neg_eq_add, ← two_smul ℂ _,smul_smul, inv_mul_cancel₀ (by norm_num),one_smul]
  rw [(lows a).1,(lows a).2,star_sub,star_one]
  change (2:ℂ)⁻¹ • ((1-star F)*(1-F))+P*((2:ℂ)⁻¹ • (F-star F))=1-((2:ℂ)⁻¹ • (1-P)*F+(2:ℂ)⁻¹ • (1+P)*star F)
  refine (show Function.Injective (fun x : Sheet n=> (2:ℂ) • x) from smul_right_injective (Sheet n) (show (2 : ℂ)≠0 by norm_num) ) ?_
  simp only [Matrix.smul_mul,Matrix.mul_smul,mul_sub,sub_mul,add_mul,hu,one_mul,mul_one,smul_sub,smul_add,smul_smul,mul_inv_cancel₀ (show (2:ℂ) ≠0 by norm_num),one_smul,two_smul]; abel
lemma rose (U : Grid n) : wood P t (.top j) U=bareD t U 0:=by unfold wood bareD; simp only [w_branch, Complex.ofReal_zero,zero_smul,zero_add]
end YM.QCD.Pine
