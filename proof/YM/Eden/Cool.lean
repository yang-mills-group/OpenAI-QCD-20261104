import YM.Eden.Solar
/-! # Invariance through translations. Image on compressed gauge stencil ledger. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior FreeResolvent
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free
open scoped Topology BigOperators InnerProductSpace Matrix Classical
variable {G:Gauge}{k :ℕ}{c f n : Side}{H:Bed}{t:Clip}{a b:ℝ}(h:Floor H t n a b)(ha:0<a)
def cameV {k:ℕ}(o:Site n)(i:Body k n):Body k n:=(i.1+o,i.2)
abbrev shineV (k:ℕ)(o:Site n) : Matrix (Body k n) (Body k n) ℝ:= scoreP (cameV o) (fun _=>1)
lemma raysV (u:Site n): shineV k u*(shineV k u).transpose=1:=rays _ _ (fun ⟨i,a⟩ ⟨j,b⟩ h=> (Prod.ext (add_right_cancel (congr_arg Prod.fst h)) (show a=b from by unfold cameV at h; exact Prod.mk.inj h|>.2))) fun i=>mul_one _
lemma twilight (o:Site n): shineV 2 o*d 1 n=d 1 n*shineV 1 o:=by
    let Q:Matrix (Body 2 n) (Body 1 n) ℝ:=d 1 n; change _*Q=Q*_; apply Matrix.ext_of_mulVec_single; intro x; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; unfold shineV; rw [sniper,sniper]; unfold Q; funext i; obtain ⟨⟨i,p⟩,rfl⟩:= (address n).surjective i; change 1* ((d 1 n)*ᵥ _) (i+o,plaquette p)=((d 1 n)*ᵥ_) (i,plaquette p); rw[d_plaquettes,d_plaquettes]; simp only [one_mul, cameV]; rw [add_right_comm i o,add_right_comm i o] -- inference issues
local notation "R0"=> H.metric.acts n
local notation "V"=> d 1 n
include h ha
lemma lofty(o:Site n)(x y: Body 2 n): learned H n (cameV o x) (cameV o y)=learned H n x y:=by
   let S:=shineV 2 o; let T:=shineV 1 o
   have ht:S*R0*S.transpose=R0:=by
        ext ⟨x,p⟩ ⟨y,q⟩; rw [shoots,peeper]; simp only [one_mul,mul_one]; change (∑' z,if y+o=x+o+ wrap n z then H.metric p q z else 0)=(∑' z,if y=x+wrap n z then H.metric p q z else 0); apply tsum_congr; intro z; rw [add_right_comm x o]; simp
   have hp: S* V = V * T:= twilight o
   have hx:S*S.transpose=1:=raysV o; have hT:S.transpose*S=1:=mul_eq_one_comm.mp hx
   have hP : T.transpose * R V R0*T=R V R0:=by unfold R; have he:= congr_arg Matrix.transpose hp; rw[transpose_mul,transpose_mul] at he; change _= _; rw [Matrix.mul_assoc _ _ T]; simp only [Matrix.mul_assoc]; rw [← hp, ← Matrix.mul_assoc,he.symm]; nth_rw 1 [← ht]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc S.transpose, hT, Matrix.one_mul]; simp_rw [← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ S.transpose S, hT, Matrix.mul_one]
   have he:S* learned H n*S.transpose=learned H n:= sunlit (V) R0 ⟨fun v=> (h.uniform.1 v).1⟩ ha h.symmetric.1 _ _ (twilight o) hP (raysV o) hx
   have hh:=congr_fun (congr_fun he x) y; rw [shoots,peeper] at hh; simpa using hh -- S unification
end YM.Eden
#print axioms YM.Eden.lofty
