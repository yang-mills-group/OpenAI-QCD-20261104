import YM.QCD.Fold.Shunt
/-! # collapse averages to single rooted pin. No parity lost. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B:ℕ}{G:Ratio C F}{Q:Ratio c f}{v:Strut C}{u:Strut c}
variable {I J:Type}[DecidableEq I][Fintype I][DecidableEq J][Fintype J]
namespace Collum
variable (S: Collum f F I J D){A: Therm I Q S.small}{K:Therm J G S.big}{T: Land F J J}{Y:Pays F J J}{M:Grid F→ArrayL J J}{m:Grid f→ArrayL I I}
variable {e a r:ℝ}
lemma rim_avg (b B:ℕ)(p :J)(q:I)(U: Grid f) (V:Support f)(H:S.Receives M m)(he:Held G K K T)(hv:∀ i j,S.pi i=S.pi j → ∃ w z,S.salt (pin Q) w (fun _=>1) z A K ∧ Warrant (raise G w) z 1 ∧ K.shiftP w i=j):
  S.cloud T b B (S.pi p) q V (settled U)=∑ j∈parcel S.pi q,∑ y,floret S.T S.d (S.rim p j) b B (S.big p) (S.big j) y (T p j y) V (settled U):=by
    let X x:= ∑ j∈parcel S.pi q,∑ y,floret S.T S.d (S.rim x j) b B (S.big x) (S.big j) y (T x j y) V (settled U)
    have ht i (hi:i∈parcel S.pi (S.pi p)):X i=X p:=by obtain ⟨w,z,hq,hT,hW⟩:= hv i p ((posted ..).1 hi); rw [← hW]; exact left_trip S _ hq hT he b B i q U V
    simp only [cloud,Pi.smul_apply,Finset.sum_apply]; rw [sum_congr rfl ht,sum_const,H.foldP,← Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀ (show (D:ℝ)≠0 from (Nat.cast_pos.mpr S.height).ne')]
lemma aft_avg (b B:ℕ)(p :J)(q:I)(U: Grid f) (V:Support f)(H:S.Receives M m)(he:Held G K K T)(hv:∀ i j,S.pi i=S.pi j → ∃ w z,S.salt (pin Q) w (fun _=>1) z A K ∧ Warrant (raise G w) z 1 ∧ K.shiftP w i=j):
  S.cloud T b B q (S.pi p) V (settled U)=∑ j∈parcel S.pi q,∑ y,floret S.T S.d (S.rim j p) b B (S.big j) (S.big p) y (T j p y) V (settled U):=by
    let X x:= ∑ j∈parcel S.pi q,∑ y,floret S.T S.d (S.rim j x) b B (S.big j) (S.big x) y (T j x y) V (settled U)
    have ht i (hi:i∈parcel S.pi (S.pi p)):X i=X p:=by obtain ⟨w,z,hq,hT,hW⟩:= hv i p ((posted ..).1 hi); rw [← hW]; exact right_trip S _ hq hT he b B i q U V
    simp only [cloud,Pi.smul_apply,Finset.sum_apply]; rw [Finset.sum_comm, sum_congr rfl ht,sum_const,H.foldP,← Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀ (show (D:ℝ)≠0 from (Nat.cast_pos.mpr S.height).ne')]
lemma rentA (x y:J)(z:Site F)(hp: Pack S.big S.big a e b M r T Y)(U:Grid f)(hv:z=S.big x ∨ z=S.big y)(hk:4*B+3<f.val)(hQ:0<a):
   (∑ i∈shortZip (S.T.cut z) B,∑ w,floret S.T S.d (S.rim x y) b B (S.big x) (S.big y) w (T x y w) i (settled U))=
     S.rim x y • spoon T z B x y (settled (S.T.links U)):=by
    rw [Finset.sum_comm]; simp_rw [zip_fl S.T S.d (S.rim x y) b B U z hv hk hQ (hp.crop x y _) S.hv]; rw [← sum_filter, show univ.filter (fun j=>j∈shortZip z B)=shortZip z B from ?_, spoon, Finset.sum_apply, smul_sum]; ext; simp
lemma forks (p :J)(q:I)(U: Grid f)(hv:∀ i j,S.pi i=S.pi j → ∃ w z,S.salt (pin Q) w (fun _=>1) z A K ∧ Warrant (raise G w) z 1 ∧ K.shiftP w i=j) (H:S.Receives M m)(h:Held G K K T)(hp: Pack S.big S.big a e b M r T Y)(hk:4*B+3 < f.val) (hQ:0<a):
  let x:= S.T.cut (S.big p); spoon (S.cloud T b B) x B (S.pi p) q (settled U)=(∑ j∈parcel S.pi q,S.rim p j • spoon T (S.big p) B p j (settled (S.T.links U))) ∧
    spoon (S.cloud T b B) x B q (S.pi p) (settled U)=∑ j∈parcel S.pi q,S.rim j p • spoon T (S.big p) B j p (settled (S.T.links U)):=by
    intro x; have he R:=rim_avg S b B p q U R H h hv; have hx R:= aft_avg S b B p q U R H h hv
    constructor
    · simp only [spoon, Finset.sum_apply, he]; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; have ht:= rentA (B:=B) S p j (S.big p) hp U (Or.inl rfl) hk hQ; rw [spoon,Finset.sum_apply] at ht; exact ht
    simp only [spoon,Finset.sum_apply,hx]; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; have ht:=rentA (B:=B) S j p (S.big p) hp U (Or.inr rfl) hk hQ; rw [spoon,Finset.sum_apply] at ht; exact ht
-- Star + tape
lemma wax (b B:ℕ)(T:Land F J J)(hp:seed T=T):seed (S.cloud T b B)=(S.cloud T b B):=by
   have ht i j X P:T i j X P = J0*star (T j i X (moon P))*J0:=congr_fun (congr_fun (congr_fun (congr_fun hp.symm i) j) X) P
   have hm i: copy S.T (moon i)=moon (copy S.T i):=rfl
   have hh p q i k: loan S.d p q i b B k=loan S.d q p i b B k:=by
     have he : pool S.d p q i b B=pool S.d q p i b B:=by
       ext s; simp only [pool,mem_filter,mem_univ,true_and]; constructor <;> (rintro ⟨ha,hb,hp⟩; refine ⟨ha,hb,fun h he v hv=> hp he h _ ?_⟩; simp_all only [mem_insert,mem_singleton,or_comm])
     simp only [loan, he]
   funext i j U P; simp only [seed, cloud,Pi.smul_apply,Finset.sum_apply,star_smul,star_sum,Matrix.mul_smul,Matrix.smul_mul, Matrix.mul_sum,Matrix.sum_mul, star_trivial]; rw [Finset.sum_comm]; apply congr_arg; refine sum_congr rfl fun v _=>sum_congr rfl fun z _=>sum_congr rfl fun u _=>?_ ; simp only [floret, Pi.smul_apply, star_smul, Matrix.mul_smul,Matrix.smul_mul, star_trivial, comp_apply,Collum.rim,star_mul,star_star, hh (S.big z) (S.big v), hm]; rw [← ht]
end Collum
end YM.QCD.Folding
