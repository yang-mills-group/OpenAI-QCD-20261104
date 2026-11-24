import YM.Play.Milan
import YM.MassiveQCD.Ribbon.Shifts
/-! # bind each letter grade throughout rotations.Trailing marker algebra counts spins separately.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Anomaly
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Cove MassiveQCD.Ribbon
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T V:Type}[Fintype A][Fintype B][Fintype T][Fintype V]
variable (T) [DecidableEq T]
-- extent metadata
def breezeP (Q: Matrix A B ℂ): Matrix (A⊕T) (B⊕T) ℂ := Matrix.fromBlocks Q 0 0 1
def breezeX (Q :Matrix A A ℂ): Matrix (A⊕T) (A⊕T) ℂ:= Matrix.fromBlocks Q 0 0 0
lemma shipsT (Q:Matrix A B ℂ)(x:Alg (A⊕T)): changeVars (breezeP T Q) x=carry T (LinearMap.toContinuousLinearMap (changeVars Q).toLinearMap) x:=by
    let P:= changeVars (breezeP T Q); have hU: P.comp (fiber T) = (fiber T).comp (changeVars Q):=by
       refine ext_atoms fun i=>?_ ; unfold P; rw [AlgHom.comp_apply,fiber,embed_atom,change_atom, Fintype.sum_sum_type,AlgHom.comp_apply,change_atom,map_sum]; simp only [map_smul,embed_atom,breezeP,fromBlocks_apply₁₁,fromBlocks_apply₁₂,Matrix.zero_apply,zero_smul,sum_const_zero,add_zero]
    have hP:P.comp (quill A)=quill B:=by
       refine ext_atoms fun i=>?_ ; unfold P; rw [AlgHom.comp_apply,quill,embed_atom,change_atom,Fintype.sum_sum_type, embed_atom]
       simp only [breezeP,Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,zero_smul,sum_const_zero,zero_add,Matrix.fromBlocks_apply₂₂]; simp [Matrix.one_apply,ite_smul]
    change P x=_; rw [← rewriteR A x,map_sum,map_sum]; apply sum_congr rfl; intro j _; rw [speaks,markedOut,map_mul, markedOut]; exact congr_arg₂ _ (AlgHom.congr_fun hU _) (AlgHom.congr_fun hP _)
lemma inkT (Q:Matrix A A ℂ)(x:Alg (A⊕T)): Wand (breezeX T Q) x=carry T (Wand Q) x:=by
    let P:=Wand (breezeX T Q); have hP (Z:Finset T)(u:Alg A): P (stake A Z u)=stake A Z (Wand Q u):=by
       have hh(u:Alg A)(i:A): Creek.v (Sum.inl i) (stake A Z u)=stake A Z (Creek.v i u):=by
           have hp:vary (Sum.inl (β:=T) i) (quill A (mono Z))=0:=by
              let f:=Finset.image (Sum.inr (α:=A)) Z; exact lock _ (effects (quill A) (fun i hi=>by unfold quill; rw [embed_atom]; apply Creek.marked; exact mem_image_of_mem _ hi) _ (Rim.monoIn Z)) (show Sum.inl i∉ f by simp [f])
           rw [markedOut,markedOut]; change vary (Sum.inl i) (_*_)=_; rw [vary_mul,hp,mul_zero,add_zero]; exact congr_arg (·*_) (survives Sum.inl_injective i u)
       unfold P Wand; simp only [Fintype.sum_sum_type, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,breezeX,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,Matrix.zero_apply, zero_smul, sum_const_zero, zero_add,add_zero,map_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro b _; rw [map_smul]; exact congr_arg (fun v=>Q i b • v) ((congr_arg (Creek.v _) (hh u i)).trans (hh _ b))

    change P x=_; rw [←rewriteR A x,map_sum,map_sum]; exact sum_congr rfl fun i _=> Eq.trans (hP ..) (speaks T ..|>.symm)
lemma rosebuds (Q : Matrix A A ℂ)(x:Alg (A⊕T)): birth (Wand (breezeX T Q)) x=carry T (birth (Wand Q)) x:=by
    have h (j: Finset T)(y:Alg A): birth (Wand (breezeX T Q)) (stake A j y)= stake A j (birth (Wand Q) y):=by
        let X:=Wand (breezeX T Q); let Z:=Wand Q; have he i : (X^i:EndA (A⊕T)) (stake A j y)= stake A j ((Z^i:EndA A) y):=by
            induction i with
            | zero=> simp
            | succ i hh=> rw [pow_succ',pow_succ',ContinuousLinearMap.mul_apply,hh]; unfold X; rw [inkT,speaks]; rfl
        refine (Stays.birther X _).unique (((stake A j).hasSum (Stays.birther Z y)).congr_fun ?_); intro i; simp only [ContinuousLinearMap.smul_apply,he]; exact (map_smul ..).symm
    rw [←rewriteR A x,map_sum,map_sum]; apply sum_congr rfl; intro i _; rw [h,speaks]
-- identifying general Q contracts on raw matrices; Pairs of species
-- note F pair-positive stroke psi->bar.
abbrev stamping (Q:Matrix A A ℂ) : Matrix (Pairs A) (Pairs A) ℂ:= Matrix.fromBlocks 0 Q 0 0
omit [DecidableEq T] in
lemma prong (Q:Matrix A A ℂ) : Wand (stamping Q)= pond (Embedding.refl (Pairs A)) Q :=by
     apply ContinuousLinearMap.ext; intro x; unfold Wand; unfold Pairs; simp only [Fintype.sum_sum_type, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply, stamping, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,Matrix.zero_apply, zero_smul, sum_const_zero,zero_add,add_zero]; unfold pond; simp only [ContinuousLinearMap.sum_apply]; rfl
lemma rimy (Q: Matrix A A ℂ) (f:Matrix A B ℂ)(x: Patio (A⊕T)): (splash (breezeP T f) (breezeX T Q) x).val= carry T ((changeVars f).toLinearMap.toContinuousLinearMap.comp (birth (Wand Q))) x.val:=by
    change changeVars (breezeP T f) (birth _ x.val)=_; rw [shipsT,rosebuds,composes]

-- Reads on ingression: mixed wipe.
lemma pondCover (Q:Matrix A A ℂ)(f:Pairs A ↪B)(x:Dirac A): pond f Q (embed f x)=embed f (Wand (stamping Q) x):=by rw [prong]; have h i z: Creek.v (f i) (embed f z)= embed f (Creek.v i z):= survives f.injective i z; unfold pond; simp only [ContinuousLinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; simp only [ContinuousLinearMap.smul_apply]; erw [map_smul (embed f)]; change Q i j • (Creek.v (f _) (Creek.v (f _) (embed f x)))=_; rw [h,h]; rfl
lemma pondMade (Q:Matrix A A ℂ)(f:Pairs A↪B)(x:Dirac A): birth (pond f Q) (embed f x)=embed f (birth (Wand (stamping Q)) x):=by
   let H:=Wand (stamping Q); let T:=pond f Q; have he i:(T^i:EndA B) (embed f x)=embed f ((H^i: EndA (Pairs A)) x):=by
       induction i with
       | zero=>simp
       | succ i hi=> rw [pow_succ',pow_succ',ContinuousLinearMap.mul_apply,hi]; exact pondCover Q f _
   refine (Stays.birther T _).unique (((embed f).toLinearMap.toContinuousLinearMap.hasSum (Stays.birther H x)).congr_fun ?_); intro i; simp only [ContinuousLinearMap.smul_apply,he]; exact (map_smul (embed f) _ _).symm
lemma emitBy (Q: Matrix A A ℂ)(f: Matrix (Pairs A) (Pairs B) ℂ) [DecidableEq B] (x: Patio (Pairs A⊕T)) :
    let P:= LinearMap.toContinuousLinearMap (wipe A B f).toLinearMap; let H:= LinearMap.toContinuousLinearMap (near A B).toLinearMap; carry T (P.comp ((birth (pond (head A B) Q)).comp H)) x.val= (splash (breezeP T f) (breezeX T (stamping Q)) x).val:=by
        intro P H; rw [rimy]; apply congr_arg (fun p=> carry T p x.val); have hp: (wipe A B f).comp (embed (head A B))=changeVars f:=by
              apply ext_atoms; intro i; rw [AlgHom.comp_apply,embed_atom,wiper,change_atom]
        ext1 x; change wipe A B f (birth (pond (head A B) Q) (embed (head A B) x))=_; rw [pondMade]; exact AlgHom.congr_fun hp _
end YM.QCD.Anomaly
#print axioms YM.QCD.Anomaly.emitBy
