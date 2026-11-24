import YM.TorusPCAC.Geometry.Pull

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Full rectangle transfer with C interchange and five-reality -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Geometry.Switch
open QCD QCD.Lat QCD.Kit QCD.Grass Lattice Wilson Finite Finset MeasureTheory Function Filter RG Revolve Ward
open scoped Matrix Topology BigOperators Kronecker Matrix.Norms.Frobenius Classical
variable {A B : Type*} [Fintype A] [Fintype B]
variable (X U : Matrix A A ℂ) (Y V : Matrix B B ℂ)
/- want interchange sends ψ→ X ψbar, bars→ -Uᵀ ψ. -/
def shiftC := changeVars (Matrix.fromBlocks 0 X (-Uᵀ) 0)
lemma chant_psi (i : A): shiftC X U (psi i)=∑ j, X i j • bar j:=by unfold shiftC psi bar; rw [change_atom ]; simp [Fintype.sum_sum_type] -- arg name
lemma chant_bar (i : A): shiftC X U (bar i)=∑ j, -U j i • psi j:=by unfold shiftC psi bar; rw [change_atom]; simp [Fintype.sum_sum_type]
lemma flip_note (F : Dirac A): shiftC X U F= embed (Sum.swap (α:=A) (β:=A)) (adapter X (-Uᵀ) F):=by
 refine AlgHom.congr_fun (φ₂:= (embed (Sum.swap (α:=A) (β:=A))).comp (adapter X (-Uᵀ))) (ext_atoms fun i=>?_) F
 cases i with
 | inl i=> change shiftC _ _ (psi i)=embed (fun i=>i.swap) (adapter _ _ (psi i)); rw [chant_psi,adapt_psi]; simp only [map_sum,map_smul,psi,embed_atom]; rfl
 | inr i=> change shiftC _ _ (bar i)=embed (fun i=>i.swap) (adapter _ _ (bar i)); rw [chant_bar,adapt_bar]; simp only [map_sum,map_smul,Matrix.neg_apply,Matrix.transpose_apply,bar,embed_atom]; rfl
lemma tune (D:Matrix A A ℂ):shiftC X U (form D)= form (U*D*X)ᵀ:=by
 let sw:= (Sum.swap (α:=A) (β:=A))
 have he (P:Matrix A A ℂ): embed sw (form P)=form (-Pᵀ):=by
    unfold form; rw [sum_comm (f:=fun i j:A=> (-Pᵀ) i j • _)]; simp only [map_sum,map_smul,map_mul,psi,bar,embed_atom]; refine sum_congr rfl (fun i _=>sum_congr rfl fun j _=>?_); unfold sw; rw [atom_flip (Sum.swap _)]; simp only [Sum.swap_inl,Sum.swap_inr,Matrix.neg_apply,Matrix.transpose_apply,neg_smul,smul_neg]
 rw [flip_note, form_map, he, Matrix.transpose_neg,Matrix.transpose_transpose, neg_mul,Matrix.transpose_neg,neg_neg,mul_assoc]
variable [DecidableEq A] [DecidableEq B]
variable (hu : U*X=1)(hv : V*Y=1)
include hu in
lemma volume (F: Dirac A) : ber A (shiftC X U F)=ber A F:=by
 have hh:shiftC X U (gauss 1)=gauss 1:=by rw [gauss,map_weight,tune,mul_one,hu,Matrix.transpose_one]
 have he:= congr_arg (ber A) hh; unfold shiftC at *; rw [ber_rows,unit_amp,mul_one] at he; rw [ber_rows,he,one_mul]
include hu in
lemma cover : Surjective (shiftC X U):=by
 have hh: ∀ a:Dirac A, ∃ b, shiftC X U b=a:=by
    intro a; refine ⟨changeVars (Matrix.fromBlocks 0 (-Xᵀ) U 0) a,?_⟩; rw [shiftC,← AlgHom.comp_apply,← change_mul]
    have ht : (-Xᵀ)*(-Uᵀ)=1:=by rw [neg_mul_neg, ← Matrix.transpose_mul,hu,Matrix.transpose_one]
    simp [Matrix.fromBlocks_multiply,ht,hu, Matrix.fromBlocks_one]
 exact hh
local notation "L"=>whole X Y
local notation "R"=>whole U V
omit [DecidableEq A] [DecidableEq B] in
lemma near_spins (F:Dirac A): shiftC L R (near A B F)=near A B (shiftC X U F):=by
 refine AlgHom.congr_fun (φ₁:= (shiftC L R).comp (near A B)) (φ₂:= (near A B).comp (shiftC X U)) (ext_atoms fun i=>?_) F
 cases i with
 | inl i=> change shiftC L R (pass _ (psi i))=pass _ (shiftC _ _ (psi i)); rw [pass_psi,chant_psi,chant_psi]; simp [Fintype.sum_sum_type,whole]
 | inr i=> change shiftC L R (pass _ (bar i))=pass _ (shiftC _ _ (bar i)); rw [pass_bar,chant_bar,chant_bar]; simp [Fintype.sum_sum_type, whole]
omit [DecidableEq A] [DecidableEq B] in
lemma far_spins (F:Dirac B): shiftC L R (far A B F)=far A B (shiftC Y V F):=by
 refine AlgHom.congr_fun (φ₁:= (shiftC L R).comp (far A B)) (φ₂:= (far A B).comp (shiftC Y V)) (ext_atoms fun i=>?_) F
 cases i with
 | inl i=> change shiftC L R (pass _ (psi i))=pass _ (shiftC _ _ (psi i)); rw [pass_psi,chant_psi,chant_psi]; simp [Fintype.sum_sum_type,whole]
 | inr i=> change shiftC L R (pass _ (bar i))=pass _ (shiftC _ _ (bar i)); rw [pass_bar,chant_bar,chant_bar]; simp [Fintype.sum_sum_type,whole]
include hu hv
lemma interchange (F:Dirac (A⊕B)): marginal A B (shiftC L R F)=shiftC Y V (marginal A B F):=by
 apply (perfect B).injective; apply LinearMap.ext; intro i; obtain ⟨v,rfl⟩:= cover _ _ hv i; rw [perfect_apply, perfect_apply, ← map_mul, volume _ _ hv,marginal_test,marginal_test,← far_spins X U Y V v,←map_mul, volume _ _ (show R*L=1 from (by simp [whole,Matrix.fromBlocks_multiply,hu,hv,Matrix.fromBlocks_one]))]
lemma sheath_spins (b:ℝ) (Z P : Matrix B A ℂ) (h : (R*joinD b P 0*L)ᵀ=joinD b Z 0) (x : Dirac A): shiftC Y V (sheath b P x)=sheath b Z (shiftC X U x):=by
 unfold sheath; rw [map_smul,← interchange _ _ _ _ hu hv,map_mul, near_spins, gauss,map_weight,tune,h,gauss] -- test
omit hu hv
lemma moved (w:ℂ) (F:Dirac A) : shiftC X U (temp w F)=temp w (shiftC X U F):=by
 unfold shiftC temp adapter; rw [← AlgHom.comp_apply,← AlgHom.comp_apply,←change_mul,←change_mul]; simp [Matrix.fromBlocks_multiply]

variable (F:Dirac A)
omit [DecidableEq A] in
lemma cc_form (D : Matrix A A ℂ): cc (form D)=form (Twist D) :=by unfold form Twist; simp only [map_sum,map_smulₛₗ,psi,bar,cc_mul,cc_atom,Matrix.transpose_apply,Matrix.conjTranspose_apply]; rfl
omit [DecidableEq A] in
lemma cc_gauss (D : Matrix A A ℂ):cc (gauss D)=gauss (Twist D):=by
 unfold gauss
 open NormedSpace in
 suffices hh : ∀ v:Dirac A, cc (exp v)= exp (cc v) by rw [hh,cc_form];
 intro v
 have ex(k:ℕ): cc (v^k)=cc v^k:=by induction k with | zero=>simp | succ k ih=> rw [pow_succ,cc_mul,ih,pow_succ]
 have hg := (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) v).map (cc).toAddMonoidHom continuous_cc
 simp only [LinearMap.toAddMonoidHom_coe, Function.comp_def,map_smulₛₗ,ex,map_inv₀,map_natCast] at hg
 exact hg.unique (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) (cc v))
lemma cc_volume : ber A (cc F)=star (ber A F):=by
 have hh : star (coef univ (vol (univ:Finset A)))=coef univ (vol (univ:Finset A)):=by
    rcases univ_sign (A:=A) with h|h <;> simp [h]
 unfold ber; simp only [LinearMap.smul_apply,star_smul,hh]; congr 1
 change _=(starRingEnd ℂ) _; rw [← write F]; simp only [map_sum,map_smulₛₗ,cc_mono,smul_eq_mul,map_mul]; exact sum_congr rfl fun i _=> by
   by_cases h:i=univ; · subst i; simp
   rw [read_other _ _ (Ne.symm h)]; simp
lemma cc_pass {C D:Type*}[Fintype C][Fintype D](s : C→ D)(F: Dirac C): cc (pass s F)=pass s (cc F):=by
 induction F using ExteriorAlgebra.induction with
 | algebraMap k => simp [Algebra.algebraMap_eq_smul_one]
 | ι v=> rw [line_atoms (A:=Pairs C)]; simp_rw [pass,map_sum,map_smul,map_smulₛₗ, embed_atom,cc_atom, RingHom.id_apply]; simp only [embed_atom]
 | add=> simp_all
 | mul=> simp_all [cc_mul]
lemma cc_marginal (D: Dirac (A⊕ B)) : cc (marginal A B D)=marginal A B (cc D):=by
 apply (perfect B).injective; apply LinearMap.ext; intro i; obtain ⟨u,rfl⟩: ∃ u:Dirac B,i=cc u:=⟨cc i,(cc_cc _).symm⟩
 rw [perfect_apply,perfect_apply, ←cc_mul,cc_volume, marginal_test,marginal_test,far,← cc_pass,←cc_mul, cc_volume]
lemma sheath_real (Q: Matrix B A ℂ)(b:ℝ): cc (sheath b Q F)=sheath b (Twist Q) (cc F):=by
 have hg : Twist (joinD b Q 0)=joinD b (Twist Q) 0:=by
    simp only [joinD,zero_add]; simp_rw [Twist, Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_transpose]; congr 1 <;> simp [show Qᴴᵀᴴ=Qᵀ from (by ext; simp)]
 unfold sheath near; rw [map_smulₛₗ, cc_marginal,cc_mul,cc_gauss,cc_pass,hg]; simp
lemma cc_moved (w:ℝ): cc (temp (w:ℂ) F)=temp w (cc F):=by
 induction F using ExteriorAlgebra.induction with
 | algebraMap k=> simp [Algebra.algebraMap_eq_smul_one]
 | ι x=> rw [line_atoms (A:=Pairs A)]; simp only [map_sum,map_smul,map_smulₛₗ]; congr 1; ext1 i; cases i <;> simp [-Complex.coe_smul,temp,adapter,change_atom, cc_atom, Fintype.sum_sum_type,Matrix.one_apply]
 | add=>simp_all
 | mul=>simp_all [cc_mul]
end YM.TorusPCAC.Geometry.Switch

#print axioms YM.TorusPCAC.Geometry.Switch.tune
#print axioms YM.TorusPCAC.Geometry.Switch.volume
