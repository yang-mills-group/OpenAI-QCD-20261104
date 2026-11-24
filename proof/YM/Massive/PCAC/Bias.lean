import YM.Massive.PCAC.Ideal
import YM.Massive.PCAC.Pillar
import YM.QCD.Step.Wrapper
/-! Exact contact piece of PCAC commutation, one kernel, any intertwining spin/flavor variation. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
open Kit
variable [DecidableEq A][DecidableEq B]
-- with explicit DecidableEq! macros in expressions join
variable (Q:Matrix B A ℂ)
noncomputable def coat := Kit.joinD 1 Q 0
noncomputable def kernel := gauss (coat Q)
omit [Fintype A][DecidableEq A] in
lemma blocks : coat Q= Matrix.fromBlocks (Qᴴ*Q) (-Qᴴ) (-Q) (1:Matrix B B ℂ):=by simp [coat,Kit.joinD]
lemma bias (V:Sour B){U:Sour A}(he:Q*U=V*Q)(hp:U*Qᴴ=Qᴴ*V)(ht: V.trace=0)(k:Bool) : applyMark k (jointChoice U V) (kernel Q)= lap (jointChoice 0 V) (kernel Q):=by
    unfold kernel; rw [mark_gauss,lap_gauss];
    have hT: (jointChoice (0:Sour A) V * coat Q).trace= V.trace:=by rw [blocks]; simp [Matrix.trace,jointChoice,Matrix.fromBlocks_multiply,Fintype.sum_sum_type]
    rw [hT,ht,zero_smul,sub_zero]; rw [blocks]; congr 2; cases k
    · simp [jointChoice, Matrix.fromBlocks_multiply, Matrix.mul_assoc,he];
    simp [jointChoice, Matrix.fromBlocks_multiply, ←Matrix.mul_assoc,hp]
-- pass convolution often adjacent to parity-ordered product. slide near on left only
omit [DecidableEq A] in
lemma crease (x:Dirac A): sheath 1 Q x=marginal A B (near A B x*kernel Q):=by unfold Kit.sheath; rw [Complex.ofReal_one, inv_one,one_pow,one_smul]; rfl
omit [DecidableEq A][DecidableEq B] in
lemma nearLap (x:Dirac A)(V:Sour B)(X:Dirac (A⊕B)): lap (jointChoice 0 V) (near A B x*X)= near A B x * lap (jointChoice 0 V) X:=by
   rw [lap_apply,lap_apply]; simp [Fintype.sum_sum_type,jointChoice,mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
   apply congr_arg (V i j • ·); change vary (besideK A (.inl i)) (vary (besideK A (.inr j)) _) = _; simp only [vary_mul, ignores_near, zero_mul,zero_add,grade_twice]; rw [show grade (near A B x)=near A B (grade x) from pass_grade .., ignores_near,zero_mul,zero_add]; rfl
lemma lap_contact (x:Dirac A)(V:Sour B){U:Sour A}(he:Q*U=V*Q)(hp:U*Qᴴ=Qᴴ*V)(ht:V.trace=0)(hv:U.trace=0)(k:Bool) : sheath 1 Q (applyMark k U x) = applyMark k V (sheath 1 Q x) - lap V (sheath 1 Q x):=by
    unfold sheath; simp only [Complex.ofReal_one,inv_one,one_pow,one_smul]; let p:=near A B x*kernel Q
    change marginal A B (near A B _*kernel Q)=applyMark k V (marginal A B p)-lap V (marginal A B p); rw [← marginal_mark k U V p hv,← lateral_lap V p]; unfold p; rw [nearLap,LMark,markNear,bias Q V he hp ht k,map_add]; abel
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.lap_contact
