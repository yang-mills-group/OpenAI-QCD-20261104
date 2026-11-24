import YM.QCD.Fold.Volt
set_option linter.unusedSectionVars false
/-! # phase-correct replica via Collum. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B:ℕ}{G:Ratio C F}{Q:Ratio c f}{v:Strut C}{u:Strut c}
variable {I J:Type}[DecidableEq I][Fintype I][DecidableEq J][Fintype J]
lemma agreeP (X:Window f F D) (H: v.1=u.1) (h:X.cut ∘ act (raise G v)= act (raise Q u) ∘ X.cut) (Z:Grid f): sky (raise G v) (X.links Z)=X.links (sky (raise Q u) Z):=by
   funext i; unfold sky pull raise; dsimp only; rw [X.read,H] -- H mutates aff coordinates, need special
   apply congr_arg; have hh : X.cut (affine v.1 (G.embed v.2) i.1)= affine u.1 (Q.embed u.2) (X.cut i.1) := congr_fun h i.1; rw [H] at hh; exact hh
-- use orientation p signs then commute hom
namespace Collum
variable (S: Collum f F I J D){A:Therm I Q S.small}{K:Therm J G S.big} (d:Site F→ℂ)(t:Spike)(k:Site f→ℂ)
def salt (u:Strut c)(v:Strut C)(k:Site f→ℂ)(d:Site F→ℂ) (A:Therm I Q S.small)(K:Therm J G S.big) :=
   v.1=u.1 ∧ S.T.cut ∘ act (raise G v)= act (raise Q u) ∘ S.T.cut ∧ (∀ i,S.pi (K.shiftP v i)=A.shiftP u (S.pi i)) ∧
   ∀ i, k (S.T.cut (S.big i))*S.orient i=d (S.big i)*S.orient (K.shiftP v i)
variable (ha:Quaint S.T d) -- oops d conflict remove
variable (hp:Warrant (raise G v) d t) (hd:Warrant (raise Q u) k t)
variable (H:S.salt u v k d A K) {X: Land F J J}(he:Held G K K X)
lemma pump {x y l q s s' m n:ℂ}(hp:m*m=1) (ht:n*n=1) (hy:s*s=1)(hz:s'*s'=1)(hx:m*x=s*l)(hw:n*y=s'*q)(A B C:Bundle):
    (star x*y) • ((s • A)*B*star (s' • C))= (m • A) * ((star l*q) • B) * star (n • C) :=by
   rcases mul_self_eq_one_iff.mp hp with rfl|h1 <;> rcases mul_self_eq_one_iff.mp ht with rfl|h2 <;> rcases mul_self_eq_one_iff.mp hy with rfl|h3 <;> rcases mul_self_eq_one_iff.mp hz with rfl|h4 <;> simp_all [neg_eq_iff_eq_neg]
include hp hd he H
lemma pence (i j:J)(Y: Grid f)(b B:ℕ)(p:Support F)(r:Support f):
  floret S.T S.d (S.rim i j) b B (S.big i) (S.big j) p (X i j p) r (settled (sky (raise Q u) Y))=
   lightP (raise Q u) t k (S.small (S.pi i))* floret S.T S.d (S.rim (K.shiftP v i) (K.shiftP v j)) b B (S.big (K.shiftP v i)) (S.big (K.shiftP v j)) (raiseS G v p) (X (K.shiftP v i) (K.shiftP v j) (raiseS G v p)) (raiseS Q u r) (settled Y) *star (lightP (raise Q u) t k (S.small (S.pi j))):=by
   have hv z : d z*d z=1:=by rcases hp.1.sign z with h|h <;> rw [h] <;> simp
   have hx z : k z*k z=1:=by rcases hd.1.sign z with h|h <;> rw [h]<;> simp
   have hm:= H.2.2.2; have hh:= pump (hx _) (hx _) (hv _) (hv _) (hm i) (hm j)
   have hp' := radS he hp (S.T.links Y) i j p
   have hr : (Macrame.splitter S.d) ∘ act (raise G v)= act (raise Q u) ∘ Macrame.splitter S.d:=by rw [S.hv]; exact H.2.1
   unfold floret; rw [K.bills,K.bills, flips hr]; simp only [Pi.smul_apply,comp_apply,← pose, ← agreeP S.T H.1 H.2.1,hp']; rw [Matrix.mul_smul,Matrix.smul_mul]; apply congr_arg; simp only [S.nest]; exact hh _ _ _ -- assoc
lemma earns (b B:ℕ) (i j:I)(r:Support f)(V:Grid f):
  S.cloud X b B i j r (settled (sky (raise Q u) V)) = lightP (raise Q u) t k (S.small i)*S.cloud X b B (A.shiftP u i) (A.shiftP u j) (raiseS Q u r) (settled V)*star (lightP (raise Q u) t k (S.small j)) :=by
   simp only [cloud,Pi.smul_apply,Finset.sum_apply]
   simp_rw [ranked H.2.2.1]; rw [Matrix.mul_smul,Matrix.smul_mul]; apply congr_arg; simp_rw [Matrix.mul_sum,Matrix.sum_mul]; refine sum_congr rfl fun p hi=>sum_congr rfl fun q hj=>?_; have he':= fun s=> pence S d t k hp hd H he p q V b B s r; rw [(posted ..).1 hi,(posted ..).1 hj] at he'; simp_rw [he']; symm; rw [← Equiv.sum_comp (raiseS G v)]
omit hp hd H
lemma holds (hv:∀ u:Strut c,∀ (r:Site f→ℂ)(P:Spike), Warrant (raise Q u) r P→ ∃ w l, Warrant (raise G w) l P ∧ S.salt u w r l A K)(b B:ℕ): Held Q A A (S.cloud X b B):=by
   apply chargedH; intro u r T V ht; obtain ⟨w,l,hp,hq⟩:= hv u r T ht; intro i j s; exact earns S _ T _ hp ht hq he b B i j s V
end Collum
end YM.QCD.Folding
