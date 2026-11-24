import YM.QCD.Fount.Bust
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Lat Octave Kit Leaf Tee Port Garden Transfer Orbit Birth Raft LeafM Run
open Eyrie Stationary Quarry Work.F03 Matrix Flume Pine Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Bay
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
open Raft.ParcelR Cost
variable {j k m B:ℕ}{P:Plan j}{w D v r b C p a t A s T d R :ℝ}{f c:Side}
variable {X:St f} {F:Flight j k}{e:f.val=c.val*F.L.val}
local notation "Y"=>houseK p X
lemma immune (m:ℝ) (x:Grid f)(hg: Species F e D R r b C B X)(hp:Species F e D R r b C B (houseK m X)):
   inverser X x - inverser (houseK m X) x= (m:ℂ) • (inverser X x * inverser (houseK m X) x):=by
   let H:=X x; let S:=houseK m X x; have he: (m:ℂ) • 1 = S-H:= (add_sub_cancel_left H ((m:ℂ) • (1:Sheet f))).symm
   calc _= H⁻¹*(S-H)* S⁻¹:= by rw [Matrix.mul_sub,Matrix.sub_mul, Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (hp.sole x),Matrix.nonsing_inv_mul _ (hg.sole x),Matrix.one_mul,Matrix.mul_one]; rfl
        _ = _ :=by rw [← he,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]; rfl
abbrev uplift (m:ℝ)(X:St f)(F:Flight j k)(e:f.val=c.val*F.L.val):Grid f→Sheet c:= foam F e (houseK m X)-foam F e X
abbrev burr (m:ℝ) (X:St f)(F:Flight j k)(e:f.val=c.val*F.L.val)(U:Grid f):= uplift m X F e U-(m:ℂ) • (leftL F e X U * rightL F e X U)
lemma hail (m:ℝ) (U:Grid f)(hg: Species F e D R r b C B X)(hp:Species F e D R r b C B (houseK m X)): uplift m X F e U=(m:ℂ) • (leftL F e X U * rightL F e (houseK m X) U) :=by
    let Q:= tied F e 0 U; let S:=inverser X U; let T:=inverser (houseK m X) U
    change 1-Q*T*Qᴴ-(1-Q*S*Qᴴ)=(m:ℂ) • _
    rw [show 1-Q*T*Qᴴ-(1-Q*S*Qᴴ)=Q*(S-T)*Qᴴ by rw [Matrix.mul_sub, Matrix.sub_mul]; abel,show S-T=_ from immune m U hg hp,Matrix.mul_smul,Matrix.smul_mul]; apply congr_arg; change Q*(S*T)*Qᴴ=Q*S*(T*Qᴴ); simp [Matrix.mul_assoc]
lemma drift (m:ℝ)(U:Grid f)(hg: Species F e D R r b C B X)(hp:Species F e D R r b C B (houseK m X)): burr m X F e U=(- (m:ℂ)^2) • (leftL F e X U *inverser X U * rightL F e (houseK m X) U) :=by
    unfold burr; rw [hail m U hg hp]; let T:=leftL F e X U; let I:=rightL F e (houseK m X) U; let S:=rightL F e X U; let W:= (tied F e 0 U)ᴴ; let X₀:=inverser X U
    have ht:S-I=(m:ℂ) • (X₀* I):=by
       unfold S I rightL; rw [← Matrix.sub_mul,immune m _ hg hp,Matrix.smul_mul,Matrix.mul_assoc]
    change (m:ℂ) • (T*I) - _ = - _ • _
    rw [← smul_sub,← Matrix.mul_sub,← neg_sub S I,ht,Matrix.mul_neg,Matrix.mul_smul,smul_neg,smul_smul,neg_smul,← Matrix.mul_assoc,pow_two]
lemma unfelt (hr:0 < r)(hg: Species F e D R r b C B X)(hp:Species F e D R r b C B Y)(ht:0≤b): Heritage (sliceL F e).embed (sliceL F e).embed r b B (uplift p X F e) (|p| *(R*R)) ∧ ∀ U, ‖burr p X F e U‖ ≤ |p|^2*(R*R*R):=by
    let S:=sliceL F e; have hx:0≤R:=hg.forest.le
    refine ⟨?_,fun i=>?_⟩
    · have h:= (hg.links.meet hp.reigns hr ht hx hx).scalar (p:ℂ); have hv: ‖(p:ℂ)‖=|p|:=(by rw [Complex.norm_real,Real.norm_eq_abs]); rw [hv] at h
      convert! h using 1; exact funext fun U=> hail p U hg hp
    rw [drift p i hg hp,norm_smul,norm_neg, norm_pow,Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (((hg.links.meet hg.hashed hr ht hx hx).meet hp.reigns hr ht (mul_nonneg hx hx) hx).value hr ht (by positivity) i) (sq_nonneg _)
lemma pale (S:Offer 1 t C)(J:Offer 2 b A)(p:ℝ):let Z:= park F e P S J p 0; leftL F e Z 1*rightL F e Z 1=barP F e * proton F e:=by
    intro Z; have he :Z 1=father F e:=by unfold Z park pesto trunkM blossomT; simp only [Pi.add_apply, Complex.ofReal_zero,zero_smul, add_zero]; rw [Fork.pale _ (by omega),Fork.pale _ (by omega),tree_zero,add_zero,add_zero]
    unfold leftL rightL inverser; rw [he]; rfl
end YM.QCD.Fount
