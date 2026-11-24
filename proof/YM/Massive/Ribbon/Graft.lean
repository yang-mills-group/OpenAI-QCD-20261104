import YM.Massive.Ribbon.Cardinal
/-! # Concrete adjunction on forms of spin jets and mixed coordinates,
faithful to the axis reflection germ (including order reversal). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset
open QCD QCD.Lat Lattice Grass TensorProduct
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ComplexOrder TensorProduct Kronecker Classical
variable {d:ℕ}(u:su.El)(a:Axis)
local notation "T" => SpinMode d
local notation "K" => starRingEnd ℂ
section CoeffBar
variable {l m n o p: Type*}
abbrev Mstar (A:Matrix m n ℂ) : Matrix m n ℂ:= A.map K
lemma mstar (A:Matrix m n ℂ)(i:m)(j:n): Mstar A i j=star (A i j):=rfl
lemma mstar_sq (A:Matrix m m ℂ): Mstar A=(star A).transpose:=rfl
lemma mstar_again (A:Matrix m n ℂ): Mstar (Mstar A)=A:=by ext; simp [Mstar]
lemma mstar_mul [Fintype n] (A:Matrix m n ℂ)(B:Matrix n p ℂ): Mstar (A*B)=Mstar A*Mstar B:=Matrix.map_mul
lemma mstar_diag (S:Matrix l m ℂ)(b:Matrix p n ℂ) : Mstar (fromBlocks S 0 0 b)=fromBlocks (Mstar S) 0 0 (Mstar b):=by ext (i|i) (j|j) <;> simp [Mstar]
lemma mstar_swap (S:Matrix l n ℂ)(b:Matrix p m ℂ) : Mstar (fromBlocks 0 S b 0)=fromBlocks 0 (Mstar S) (Mstar b) 0:=by ext (i|i) (j|j) <;> simp [Mstar]
lemma dagger_change [Fintype m][Fintype n](A:Matrix m n ℂ)(x: Alg m): dagger (changeVars A x)=changeVars (Mstar A) (dagger x):=by
    induction x using ExteriorAlgebra.induction with
    | algebraMap s=> simp [Algebra.algebraMap_eq_smul_one,dagger_one]
    | ι v=> rw [line_atoms (A:=m)]; simp_rw [map_sum,map_smul,map_smulₛₗ, dagger_atom,change_atom,map_sum,map_smulₛₗ,dagger_atom]; rfl
    | add x y hx hy=> simp_rw [map_add,hx,hy]
    | mul x y hx hy=>rw [map_mul,dagger_mul,dagger_mul,map_mul,hx,hy]
lemma mstar_wave (X:Spike) : Mstar (wave X)=wave (Mstar X):=by rw [mstar_sq,mstar_sq,wave_star,wave_tr]
lemma mstar_glide (X:Spike) : Mstar (flipTable (d:=d) a X)=flipTable a (Mstar X):=by
   ext i j; simp only [flipTable, spinTable, Mstar, Matrix.of_apply, Matrix.map_apply]; conv_rhs=> rhs; rw [←mstar_wave X]
   rw [map_mul,map_pow,map_neg,map_one]; split <;> simp
end CoeffBar
abbrev eyeW (d:ℕ)(a:Axis) : Matrix (Pairs (SpinMode d)) (Pairs (SpinMode d)) ℂ:= fromBlocks 0 (flipTable a (-(gamma a).transpose)) (flipTable a (-gamma a)) 0
lemma eyeTracks (i j:Pairs T)(h:letterWeight i≠letterWeight j): eyeW d a i j=0:=by
    obtain ⟨p,hp⟩:= EuPin.choice (Signed.mirror a); unfold eyeW; rw [hem_turn _ hp,hem_turn _ hp]; rcases i with i|i <;> rcases j with j|j; · rfl
    · exact trails _ _ _ _ h
    · exact trails _ _ _ _ h
    rfl
lemma glimmer (X Y:Spike) : flipTable (d:=d) a X * flipTable a Y=spinTable (X*Y):=by
    obtain ⟨p,hp⟩:= EuPin.choice (Signed.mirror a); have h: p⁻¹.Lifts (Signed.mirror a):=by change p.coord⁻¹=(Signed.mirror a).ortho; rw [hp]; exact (map_inv Signed.inclusionO (Signed.mirror a)).symm -- maybe no goals
    rw [hem_turn _ hp, hem_turn _ h, reel, inv_mul_cancel,wave_mul,under_spin]
lemma eyeCompletion (d:ℕ) : Mstar (eyeW d a)*eyeW d a=1:=by
    unfold eyeW; rw [mstar_swap,mstar_glide,mstar_glide,fromBlocks_multiply, glimmer,glimmer]; rw [mstar_sq,mstar_sq, star_neg, star_neg]; rw [show star (gamma a).transpose=(gamma a).transpose from congr_arg transpose (gamma_star a), gamma_star]; rw [transpose_neg,transpose_neg,transpose_transpose, neg_mul_neg,neg_mul_neg, Lat.gamma_sq,←transpose_mul, Lat.gamma_sq, transpose_one]; simp; congr; exact Subsingleton.elim .. -- star lemma names
lemma eyeColors (d:ℕ) : Mstar (noir u d) * eyeW d a= eyeW d a*noir u d:=by
    let V:=colorTable (d:=d) u; let W:=Mstar V; let X:=flipTable (d:=d) a (-(gamma a).transpose); let Y:=flipTable (d:=d) a (-gamma a); change Mstar (fromBlocks V 0 0 W)*fromBlocks 0 X Y 0=fromBlocks 0 X Y 0*fromBlocks V 0 0 W
    have hv:V*Y=Y*V:=by obtain ⟨p,hp⟩:= EuPin.choice (Signed.mirror a); unfold V Y; rw [hem_turn _ hp,groom,reel,reel,(interlace ..).eq,one_mul,mul_one]
    have hw:W*X=X*W:=by
       obtain ⟨p,hp⟩:= EuPin.choice (Signed.mirror a); unfold W V X; rw [mstar_sq,←mono_color, hem_turn _ hp,groom, reel,reel,(interlace ..).eq, one_mul,mul_one]
    rw [mstar_diag, show Mstar W=V from mstar_again V,fromBlocks_multiply,fromBlocks_multiply,show Mstar V = W from rfl,hv,hw]; simp

private abbrev aG (a:Axis) : GPol→ₛₗ[starRingEnd ℂ]GPol:= (Labels.rotated (Signed.reflect a)).toLinearMap.comp conjGPol
abbrev aSpin (d:ℕ)(a:Axis) : SpinPol d→ₛₗ[starRingEnd ℂ] SpinPol d:= (changeVars (eyeW d a)).toLinearMap.comp dagger
lemma spin_wagon : Function.Involutive (aSpin d a):=by intro x; change changeVars _ (dagger (changeVars _ (dagger x)))=_; rw [dagger_change,multipleChange, eyeCompletion, change_one,dagger_invol]; rfl
lemma conj_values (x:GPol)(J:Labels.Jet su): Labels.read J (conjGPol x)=star (Labels.read J x):= Labels.conj_value ..
lemma conj_mobil (e:(n:ℕ)→ Module.End ℝ (Labels.Taylor su n))(x:GPol): Labels.changed e (conjGPol x)=conjGPol (Labels.changed e x):= by apply Labels.eval_ext; intro J; rw [conj_values,Labels.eval_changed,Labels.eval_changed,conj_values]
private lemma a_gon : Function.Involutive (aG a):=by
    intro x; let V:= Labels.rotated (Signed.reflect a) (G:=su); let y:=conjGPol x; change V (conjGPol (V y))=_
    have hv: conjGPol y=x:= by apply Labels.eval_ext; intro J; rw [conj_values,conj_values _ J, star_star]
    rw [show conjGPol (V y)=V (conjGPol y) from (conj_mobil _ y).symm,hv]; unfold V; rw [← Labels.rotation_law]; rw [show Signed.reflect a * Signed.reflect a=1 from ?_, burns]; change Signed.inclusionO _ * Signed.inclusionO _= _; rw [← map_mul Signed.inclusionO,show Signed.mirror a*Signed.mirror a=1 from mul_inv_cancel _, map_one]
lemma eyeTwist : Function.Involutive (adj (d:=d) a):=by
    intro x; induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul x y=> unfold adj; simp_rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) (a_gon a x) (spin_wagon a y)
    | add x y hx hy=> simp only [map_add,hx,hy]
lemma eye_dance (x: Pol d) : adj a (colorAct u x)= colorAct u (adj a x):=by
    induction x using TensorProduct.induction_on with
    | zero=> simp
    | tmul x y=>
        unfold adj colorAct; simp_rw [TensorProduct.map_tmul]; apply congr_arg₂ (tmul ℂ)
        · let z:=conjGPol x; change Labels.rotated (Signed.reflect a) (conjGPol (dyesG u x))= dyesG u (Labels.rotated _ z); rw [←conj_mobil]; unfold dyesG Labels.rotated; apply Labels.eval_ext; intro J; simp_rw [Labels.eval_changed]; apply congr_arg (fun J=>Labels.read J z); funext i; exact Labels.Taylor.turn_paint ..
        change changeVars (eyeW _ _) (dagger (changeVars (noir _ _) y))=changeVars (noir _ _) (changeVars (eyeW _ _) (dagger y)); rw [dagger_change, multipleChange, multipleChange, eyeColors]
    | add x y hx hy=> simp only [map_add,hx,hy]
lemma eye_cap (x:Pol d)(h:x∈cap d) : adj a x∈cap d:=by
   refine Submodule.span_induction (p:=fun x _=> adj a x∈ cap d) ?_ ?_ ?_ ?_ h
   · rintro _ ⟨⟨p,s⟩, hp,rfl⟩; unfold gen adj; rw [TensorProduct.map_tmul]; change Labels.rotated _ (Labels.conjPol (MvPolynomial.monomial p 1)) ⊗ₜ[ℂ] (changeVars (eyeW d a) (dagger (mono s)))∈ _; rw [Labels.conjPol,MvPolynomial.map_monomial,map_one]; exact pump _ _ (Rim.step _ (f:=(changeVars _).toLinearMap) (Rim.keeps letterWeight (eyeTracks a)) (Rim.dkeeps _ _ _ rfl)) (billups _ _ _ _ hp)
   · rw [map_zero]; exact Submodule.zero_mem _
   · intro _ _ _ _ he ht; rw [map_add]; exact Submodule.add_mem _ he ht
   intro c x _ h; rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ h
lemma label_eye (x:Label d): adj a x.val ∈ labels d:=by
   have h:= (label_law _).mp x.property; exact (label_law _).mpr ⟨ eye_cap a _ h.1, fun u=> (eye_dance u a x.val).symm.trans (by rw [h.2])⟩
noncomputable def adjCore (d:ℕ):Label d≃ₛₗ[starRingEnd ℂ]Label d where
   toFun x:=⟨_,label_eye a x⟩
   invFun x:=⟨_,label_eye a x⟩
   left_inv x:=Subtype.ext (eyeTwist a x.val)
   right_inv x:=Subtype.ext (eyeTwist a x.val)
   map_add' x y:=Subtype.ext (map_add (adj a) x.val y.val)
   map_smul' u x:=Subtype.ext (map_smulₛₗ (adj a) u x.val)
end YM.Massive.UV
#print axioms YM.Massive.UV.adjCore
