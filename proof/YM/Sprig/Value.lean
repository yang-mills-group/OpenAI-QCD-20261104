import YM.Sprig.Chloe
import YM.Tarn.Nacre
import YM.Tarn.Stamen
/-! # Unit measure for invariant raw-system before Pin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig.Chloe
open Function Filter Matrix Set Finset QCD QCD.Lat QCD.Grass QCD.Creek
open scoped BigOperators Topology Classical Matrix Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Kronecker
variable {X:Type}[Fintype X] {Y:Type}[Fintype Y]
lemma deg_sign (s:Finset X):∃ t:ℂ,(t=1 ∨ t = -1) ∧ dagger (mono s)=t • mono s:=by
    induction s using Finset.induction_on with
    | empty=> exact ⟨1,Or.inl rfl,by rw[mono_empty,dagger_one,one_smul]⟩
    | insert a s h ih=>
      obtain ⟨r,hR,hP⟩:=ih; have h1:= mono_mul_sign {a} s (by simpa using h)
      have h2:=mono_mul_sign s {a} (by simpa using h); simp only [Finset.disjUnion_eq_union,mono_single,Finset.singleton_union,show s ∪ {a} =insert a s from ((Finset.union_comm ..).trans (Finset.singleton_union ..))] at h1 h2
      rcases hR with hR|hR <;> rw [hR] at hP
      · rw [one_smul] at hP; have hv: dagger (atom a * mono s)= mono s * atom a:=by rw [dagger_mul,dagger_atom,hP]
        rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> simp only [h1,h2,map_neg] at hv
        · exact ⟨1,Or.inl rfl,by rw[one_smul,hv]⟩
        · exact ⟨-1,Or.inr rfl,by rw[neg_one_smul,hv]⟩
        · exact ⟨-1,Or.inr rfl,by rw [neg_one_smul]; exact neg_inj.mp (hv.trans (neg_neg _).symm)⟩
        · exact ⟨1,Or.inl rfl,by rw [one_smul]; exact neg_inj.mp hv⟩
      rw [neg_one_smul] at hP; have hv: dagger (atom a * mono s)= -(mono s * atom a):=by rw[dagger_mul,dagger_atom,hP,neg_mul]
      rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> simp only [h1,h2,map_neg,neg_neg] at hv
      · exact ⟨-1,Or.inr rfl,by rw[neg_one_smul,hv]⟩
      · exact ⟨1,Or.inl rfl,by rw [one_smul,hv]⟩
      · exact ⟨1,Or.inl rfl,by rw [one_smul]; exact neg_inj.mp hv⟩
      · exact ⟨-1,Or.inr rfl,by rw [neg_one_smul]; exact neg_inj.mp (hv.trans (neg_neg _).symm)⟩
lemma shivery (x y:Alg X): poly (dagger x) (dagger y)=star (poly x y):=by
    rw [← write x, ← write y,map_sum,map_sum,lunarL,lunarL,star_sum]; apply sum_congr rfl; intro i _; rw [lunar,lunar,star_sum]; apply sum_congr rfl; intro j _; simp_rw [map_smulₛₗ,senseL,sense,star_mul']; apply congr_arg; apply congr_arg₂ HMul.hMul rfl -- reduce star coefficients. Lean.
    choose t ht hP using fun i:Finset X=>deg_sign i; simp_rw[hP,senseL,sense,Chloe.polar]; split_ifs with h; subst j; rcases ht i with hx|hx<;>rw[hx]<;>simp; simp
variable [DecidableEq X]
lemma swap_disp(W: Type)[Fintype W][DecidableEq W](x y:Dirac W): poly (embed (Sum.swap (α:=W)) x) (embed Sum.swap y)=poly x y :=by
    let I:= (1:Matrix W W ℂ); let M: Matrix (W ⊕ W) (W ⊕ W) ℂ:=fromBlocks 0 I I 0; have h:M∈unitary _:=by
        have he:star M=M:=by unfold M I; simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]; -- Check
        have hh:M*M=1:=by unfold M I; simp [fromBlocks_multiply, Matrix.fromBlocks_one]
        exact ⟨by rw[he]; exact hh,by rw[he]; exact hh⟩
    have hf: embed (Sum.swap (α:=W ) (β:=W))= changeVars M:= by
         refine ext_atoms fun i=>?_ ; cases i<;> rw [change_atom, embed_atom] <;> simp [M,I, Fintype.sum_sum_type,Matrix.one_apply]; -- Atom rec
    rw[hf]; exact saturates M h x y
lemma tilt_unitary {A: Matrix X X ℂ}(h:A∈unitary _) : A.transpose∈unitary _:=by
      have hp:star A.transpose=(star A).transpose:=rfl; have ht: Aᵀ * star Aᵀ =1:=by rw[hp,← Matrix.transpose_mul, h.1]; simp -- notation ambiguate star Aᵀ means star(Aᵀ)
      refine ⟨?_,ht⟩; rw [hp,← Matrix.transpose_mul,h.2]; simp
lemma negU{A:Matrix X X ℂ}(h:A∈unitary _): -A∈unitary _:=⟨by rw[star_neg,neg_mul_neg]; exact h.1,by rw [star_neg,neg_mul_neg]; exact h.2⟩
lemma adapters {A B:Matrix X X ℂ}(x y:Dirac X)(hp:A∈unitary _)(hq:B∈unitary _):poly (adapter A B x) (adapter A B y)=poly x y:=by
      
      let P:= Matrix.fromBlocks A 0 0 B; have hh:star P= Matrix.fromBlocks (star A) 0 0 (star B):=by unfold P; simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
      have hp:P ∈unitary _ := by constructor <;> rw [hh] <;> unfold P <;> simp [fromBlocks_multiply,hp.1,hq.1,hp.2,hq.2, fromBlocks_one]
      exact saturates P hp x y
lemma litP {A:Matrix X X ℂ}(x y: Dirac X)(hp:A∈unitary _):poly (Grass.tilt A x) (Grass.tilt A y)=star (poly x y):=by rw [tilts,tilts,adapters _ _ (negU hp) (tilt_unitary (negU hp)),turn,LinearMap.comp_apply,LinearMap.comp_apply]; exact (swap_disp _ _ _).trans (shivery x y)
lemma costume {A:Matrix X X ℂ}(x y:Dirac X)(hp:A∈unitary _):poly (Kit.disguise A x) (Kit.disguise A y)=poly x y:= adapters _ _ hp (tilt_unitary (Unitary.star_mem hp))
lemma baseCharge {A B: Matrix X X ℂ}(x y:Dirac X)(hp:A∈unitary _)(hq:B∈unitary _):poly (TorusPCAC.Geometry.Switch.shiftC A B x) (TorusPCAC.Geometry.Switch.shiftC A B y)=poly x y:=by
      rw [TorusPCAC.Geometry.Switch.flip_note,TorusPCAC.Geometry.Switch.flip_note]; exact (swap_disp _ _ _).trans (adapters _ _ hp (negU (tilt_unitary hq)))
lemma gradeSum(x y:Alg X):poly (grade x) (grade y)=poly x y:=by
      let A:Matrix X X ℂ:= -1; have h:A ∈unitary _:=negU (one_mem _); suffices he: Grass.grade = changeVars A by rw[he]; exact saturates A h x y
      apply ext_atoms; intro i; rw [change_atom,grade_atom]; simp [A,Matrix.one_apply,Matrix.neg_apply]
end YM.Sprig.Chloe
#print axioms YM.Sprig.Chloe.gradeSum
#print axioms YM.Sprig.Chloe.litP
#print axioms YM.Sprig.Chloe.costume
#print axioms YM.Sprig.Chloe.baseCharge
