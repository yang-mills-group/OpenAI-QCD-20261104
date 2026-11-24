import YM.Lyre.Reach
import YM.Massive.Reservoir.Bare
import YM.Massive.Finite.Chess
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Lattice Wilson MeasureTheory Function Filter QCD.Lat QCD QCD.Grass Tide RP Plum
open scoped BigOperators Topology Matrix.Norms.L2Operator ComplexOrder Classical
variable {c:Side}{F:ℕ}{R:Cells.Cut c}
local notation "V"=> Stud c F
noncomputable def rawK (K:Regulator c F)(x:Stud c F):= joint (⇑K.density*x)
variable (K:Regulator c F)
noncomputable def valueH (K:Regulator c F)(x:Stud c F):ℂ:= K.Z⁻¹ * rawK K x
lemma known (K:Regulator c F)(x: Stud c F)(h:Tide.Stays x): Integrable (fun i=> ber _ (K.density i*x i)) (prior su c):=((((stays K.density.continuous).mult h)).flows ((ber (Modes c F)).continuous_of_finiteDimensional)).intg _
lemma spill {x y:Stud c F}(hx:Stays x)(hy:Stays y): rawK K (x+y)=rawK K x+rawK K y:=by unfold rawK joint; simp only [Pi.mul_apply, Pi.add_apply,mul_add,map_add,integral_add (known K x hx) (known K y hy)]
lemma spentH (x:Stud c F)(t:ℂ): rawK K (t • x)=t • rawK K x:=by unfold rawK joint; simp only [Pi.mul_apply,Pi.smul_apply,mul_smul_comm,map_smul,integral_smul]
lemma spend (x:Stud c F)(t:ℂ): valueH K (t • x)= t • valueH K x:=by unfold valueH; rw [spentH]; change _* (t*_)=t*(_ * _); ring
lemma spentA {x y:Stud c F}(hx:Stays x)(hy:Stays y): valueH K (x+y)=valueH K x+valueH K y:=by unfold valueH; rw [spill K hx hy,mul_add]
lemma signsV {x y:Stud c F}(h:Chess.SignedEq x y): ‖valueH K x‖ = ‖valueH K y‖:=by
    rcases h with h|h; · rw [h]
    rw [h,← neg_one_smul ℂ y, Lyre.spend]; simp
lemma blank (h:K.Z≠0):valueH K 1=1:=inv_mul_cancel₀ h
private lemma conjugate (a b z w : ℂ) (A : 0 ≤ a) (B : 0 ≤ b)
    (H : ∀ c : ℂ, 0 ≤ a+c*z+star c*w+c*star c*b) : star z=w := by
  have ha := Complex.nonneg_iff.mp A; have hb := Complex.nonneg_iff.mp B; have hr := Complex.nonneg_iff.mp (H 1); have hi := Complex.nonneg_iff.mp (H Complex.I); rw [Complex.nonneg_iff] at A B; simp [Complex.mul_im, ← A.2, ← B.2] at hr hi; apply Complex.ext <;> simp <;> linarith
lemma shears (K:Regulator c F) (ht:K.t=0) (hK:0 ≤ K.β) {x y:Stud c F}(hx:Plum.Fence R.sector x)(hy:Plum.Fence R.sector y)(hr:R.kind=.link)(hz:2≤ R.half.val) : let L (u v:Stud c F):= rawK K (tallH R u*v); ‖L x y‖^2 ≤ ‖L x x‖ * ‖L y y‖:=by -- implicit x
    intro L; have hv(u:V)(h:Fence R.sector u):0 ≤ L u u:=by
         change 0 ≤ joint (_ * (_*_ )); rw [← tallC u K.zeroCut (show K.zeroCut.t=0 from ht)]; exact Regulator.signed (R:=K) hr hK hz _ h
    let v:=tallH R x; let w':= tallH R y
    have ha: Stays v:= tallCost x hx.hp; have hb: Stays w':= tallCost y hy.hp
    have hm (c:ℂ)(x:V)(h:Stays x) : Stays (c • x) := h.flows (continuous_id.const_smul c)
    have H (s:ℂ) : 0 ≤ L x x+s*L x y+star s*L y x+s*star s*L y y:=by
         apply (hv _ (hx.add (hy.mass s))).trans_eq; change rawK K _=_
         rw [show tallH R (x+s • y)=v+ star s • w' from funext fun i=> by simp [huesT,v,w'], add_mul,mul_add,mul_add]
         have h1:Stays (star s • w'):=hm _ _ hb; have h2:Stays (s • y):=hm _ _ hy.hp
         have hf{u v:V}(hu:Tide.Stays u)(hv:Tide.Stays v): Tide.Stays (u+v):=(hu.both hv).flows continuous_add
         rw [spill K (hf (ha.mult hx.hp) (ha.mult h2)) (hf (h1.mult hx.hp) (h1.mult h2)), spill K (ha.mult hx.hp) (ha.mult h2), spill K (h1.mult hx.hp) (h1.mult h2)]; simp only [mul_smul_comm,smul_mul_assoc,spentH,smul_eq_mul]; unfold L v w'; ring
    have hQ:=hv x hx; have hy':=hv y hy; apply Cells.schwarz hQ hy'; intro t; have h:= H (star t); rw [star_star] at h; rw [mul_comm (star t) t, ← conjugate (L x x) (L y y) (L x y) (L y x) hQ hy' H] at h; exact h
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.shears
#print axioms YM.Massive.Lyre.signsV
