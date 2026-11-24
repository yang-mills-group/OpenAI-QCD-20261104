import YM.Massive.Ribbon.Schur
import YM.QCD.Revolve.Pin
/-!
# The hypercube part of the Euclidean Pin convention.

Existence of reflection-square choices on that subgroup in the full
Euclidean Pin definition. Will need other assertions for Lie/spacetime.
(For existence of discrete sym choices cf. `YM/QCD/Revolve/Pin.lean`, but
`Swing` there doesn't require the extra charge-C convention, so pass the central
calculation first.) -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.EuPin
open QCD QCD.Lat Lattice Wilson Mink Lorentz Function Matrix QCD.Revolve
open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology Kronecker ComplexOrder Classical
open Clifford Finset
variable (x:E4)(s:Signed)
lemma signMesh (i:Axis): Ortho.move s.ortho x (s.perm i) = if s.flip i then -x i else x i:=by rw [Signed.ortho_move]; exact Signed.act_at ..
lemma slash_axis (i:Axis): slash (Ortho.move s.ortho (basis i))=(if s.flip i then -gamma (s.perm i) else gamma (s.perm i)):=by
    unfold slash; rw [← Equiv.sum_comp (s.perm)]; simp_rw [signMesh]; rw [sum_eq_single i];
    · cases h:s.flip i <;> simp [basis]
    · intro j _ h; simp [basis,h]
    simp
lemma retains {p:EuPin}(he:p.Lifts s) : Swing s p.matrix.val:=by refine ⟨p.isUnitary,fun i=> ?_⟩; rw [act_gamma, show p.coord=s.ortho from he, slash_axis]
lemma ample (X:Spikeˣ)(hp:Swing s X.val)(hv:KeepsC X): ∃ p: EuPin, p.Lifts s ∧ p.matrix=X:=by
    let F:Ortho×Spikeˣ:= (s.ortho,X); refine ⟨⟨F,(euPin_iff _).mpr ⟨hv,fun x=> ?_⟩⟩,rfl,rfl⟩; change X.val* _= slash (Ortho.move s.ortho x)*_
    unfold slash; rw [Matrix.mul_sum,Matrix.sum_mul]; conv_rhs=> rw [← Equiv.sum_comp s.perm] -- rw second sum or first?
    apply sum_congr rfl; intro i _; rw [Matrix.smul_mul,Matrix.mul_smul, hp.sends, signMesh]; split <;> simp [F]
lemma life_mul {p q: EuPin}{s t:Signed}(h:p.Lifts s)(hp:q.Lifts t): (p*q).Lifts (s*t):=by change p.coord*q.coord=_; rw [show p.coord=_ from h,show q.coord=_ from hp]; exact (map_mul Signed.inclusionO s t).symm

def walk (X:Spike): Spike:= Complex.I • (g5 * X)
private lemma unitW {s:Signed}{X:Spike} (h: Swing s (g5*X)): Swing s (walk X):=by
    let p:=g5*X; refine ⟨Matrix.mem_unitaryGroup_iff'.mpr ?_,fun i=>?_⟩
    · unfold walk; rw [star_smul,Matrix.smul_mul,Matrix.mul_smul,h.unit.1,smul_smul]; simp
    unfold walk; rw [Matrix.smul_mul,Matrix.mul_smul,h.sends i]
private lemma age (X:Spike)(h:X*X=1)(hv:X*C= -(C*X.transpose)): walk X * C * (walk X).transpose = C :=by
    unfold walk; rw [transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,Complex.I_mul_I,neg_one_smul]; have hp:X*C*X.transpose= -C:=by rw [hv,neg_mul,Matrix.mul_assoc, ← transpose_mul, h, transpose_one, mul_one];
    simp_rw [transpose_five, Matrix.mul_assoc]; rw [← Matrix.mul_assoc C, ← Matrix.mul_assoc X, ← Matrix.mul_assoc X, hp]; rw [neg_mul,mul_neg]; -- remaining `g5`
    rw [neg_neg, ← Matrix.mul_assoc,fiveC, Matrix.mul_assoc,g5_sq,mul_one]
lemma reaching (s:Signed)(X:Spike)(h:X*X=1)(ht:X*C= -(C*X.transpose))(hv:Swing s (g5*X)) : ∃ p:EuPin, p.Lifts s ∧ p.matrix.val= walk X:=by
    let W:=walk X; let hp:= unitW hv; let x:Spikeˣ:=⟨W,star W,hp.unit.2,hp.unit.1⟩; obtain ⟨p,he,hZ⟩:= ample s x hp (age X h ht); exact ⟨p,he,congr_arg Units.val hZ⟩
lemma optic (i:Axis) : ∃ p:EuPin,p.Lifts (Signed.mirror i) ∧ p.matrix.val=(-Complex.I) • (gamma i*g5) :=by
    rw [five i, neg_smul,smul_neg,neg_neg]; exact reaching _ (gamma i) (gamma_sq _) (transC i) (Swing.mir _)

open Swing
private lemma paving (i j:Axis)(h:i≠j): ∃ p:EuPin,p.Lifts (Swing.pure (Equiv.swap i j)):=by
    let A:=gamma i; let B:=gamma j; let Z:=pearl • (A-B); have ht: A*B= -(B*A):= clifford h
    have h1:A*A=1:= gamma_sq i; have h2:B*B=1:= gamma_sq j
    have hx: Z*Z=1:=by
       unfold Z; rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul, priceP,sub_mul,mul_sub,mul_sub,h1,h2,ht,show (1:Spike)- -(B*A)-(B*A-1)=(2:ℂ) • (1:Spike) by rw [two_smul]; abel, smul_smul,inv_mul_cancel₀ (by norm_num),one_smul]
    have hZ : Z*C= -(C*Z.transpose):=by unfold Z A B; rw [Matrix.smul_mul,sub_mul,transC,transC,transpose_smul,Matrix.mul_smul,transpose_sub,mul_sub, ← smul_neg,neg_sub', sub_neg_eq_add] -- need equality inside smul maybe
    obtain ⟨p,hp,-⟩:= reaching _ Z hx hZ (Swing.switch i j h); exact ⟨p,hp⟩
theorem choice : ∃ p:EuPin,p.Lifts s:=by
    have hone:∃ p:EuPin,p.Lifts 1:=⟨1,(map_one Signed.inclusionO).symm⟩
    have he(t:Equiv.Perm Axis):∃ p:EuPin,p.Lifts (Swing.pure t):=by
      induction t using Equiv.Perm.swap_induction_on with|one=>exact hone|swap_mul f i j h ih=> obtain ⟨p,hp⟩:= ih; obtain ⟨q,hq⟩:= paving i j h; exact ⟨q*p,life_mul hq hp⟩
    have hg(v:Finset Axis):∃ p:EuPin,p.Lifts (sunday v):=by
       induction v using Finset.induction_on with
       | empty=> rw [show sunday ∅=1 by apply Signed.ext rfl; funext; simp [sunday]]; exact hone
       | insert a v hv ih=>
         obtain ⟨V,H⟩:=ih; obtain ⟨y,hy,-⟩:= optic a; rw [show sunday (insert a v)=Signed.mirror a*sunday v from ?_]; exact ⟨y*V,life_mul hy H⟩
         refine Signed.ext rfl ?_; funext i; simp only [sunday,Signed.mul_flip,Equiv.refl_apply,Signed.mirror,mem_insert]; by_cases hw:a=i <;> simp_all [Ne.symm]
    obtain ⟨p,hp⟩:= he s.perm; obtain ⟨q,hq⟩:= hg (univ.filter (s.flip ·)); refine ⟨p*q,?_⟩; set t:= Swing.pure s.perm*sunday (univ.filter (s.flip ·)); have ht:t=s:=by refine Signed.ext rfl ?_; funext i; simp [t,Swing.pure,sunday];
    exact ht ▸ life_mul hp hq
end YM.Massive.EuPin
#print axioms YM.Massive.EuPin.choice
