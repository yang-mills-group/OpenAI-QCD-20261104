import YM.Alum.Greet
import YM.Next.MAXWELL.Caps
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass Analysis
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder ContDiff
namespace Free.Sip
variable {n k r F:ℕ}{x:Points n}(hx:x∈conf n)
private lemma flies (i j: Pinor)(u:E4)(h:u≠0) : ContDiffAt ℝ ω (dirac i j) u:=by
   have hf : ContDiffAt ℝ ω Maxwell.Green u := by unfold Maxwell.Green; exact contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.inv (sq_pos_of_pos (norm_pos_iff.mpr h)|>.ne'))
   apply ContDiffAt.neg; refine ContDiffAt.sum fun a _=> contDiffAt_const.mul (?_); exact Complex.ofRealCLM.contDiff.contDiffAt.comp u (Analysis.dSmooth hf (basis a) le_top)
include hx
lemma legs (t j:Fin n)(p:SpinMode k)(q:SpinMode F)(h:t≠j): ContDiffAt ℝ ω (fun x: Points n=>Free.leg p q (x t) (x j)) x:=by
     have he:(x t-x j)≠0:=sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne h)
     unfold Free.leg; split_ifs; swap; · exact contDiffAt_const
     have h(l:List Axis): ContDiffAt ℝ ω (derivatives l (dirac p.1.2.1 q.1.2.1)) (x t-x j):= by induction l with| nil=>exact flies _ _ _ he| cons i l ih=> exact Analysis.dSmooth ih (basis i) le_top
     apply contDiffAt_const.mul; exact (h _).comp x (f:=fun y:Points n=> y t-y j) ((PiLp.proj (𝕜:=ℝ) 2 (fun _=>E4) t).contDiff.contDiffAt.sub ((PiLp.proj (𝕜:=ℝ) 2 (fun _=>E4) j).contDiff.contDiffAt))
variable (d: Fin n→ ℕ)(u:(i:Fin n)→Pol (d i))
lemma puff (i j:Occ d):ContDiffAt ℝ ω (fun x:Points n=>pair x i j) x:=by
      obtain ⟨t,p|p⟩:=i; all_goals
       obtain ⟨s,q|q⟩:=j
       all_goals by_cases he: t=s
       all_goals try -- split result
          unfold pair; simp only [he, ↓reduceIte, Sum.elim_inl,Sum.elim_inr]
       all_goals first | exact contDiffAt_const | exact legs hx t s p q he | exact (legs hx s t q p (Ne.symm he)).neg
lemma plump (l:List (Occ d))(m:ℕ):ContDiffAt ℝ ω (fun x:Points n=> pf (pair x) m l) x:=by
       induction m generalizing l with
       | zero=> cases l <;> exact contDiffAt_const
       | succ m ih=>
                    cases l with
                    | nil=>exact contDiffAt_const
                    | cons a l=>
                       refine ContDiffAt.sum fun i _=> (contDiffAt_const.mul (puff hx d a (l.get i))).mul (ih _)
lemma lemmaC (v:(i:Fin n)→PowerPair (d i)) : ContDiffAt ℝ ω (fun x=>monomialValue (u:=d) x v) x:=by
      unfold monomialValue; exact (Maxwell.Free.kernel_analytic _ hx).mul (plump hx d _ _)
lemma smoothC : ContDiffAt ℝ ω (fun p:Points n=> UV.Free.moment d p u) x:= by
    simp_rw [Multilabel.expansion (B:=fun i:Fin n=>basisU (d i)) (T:=UV.Free.moment d _) (v:=u)]
    simp_rw [smul_eq_mul]; refine ContDiffAt.sum fun i _=>contDiffAt_const.mul (?_); unfold UV.Free.moment; simp_rw [Multilabel.applyBasis]; exact lemmaC hx d i
end Free.Sip
end YM.Massive.UV
#print axioms YM.Massive.UV.Free.Sip.smoothC
