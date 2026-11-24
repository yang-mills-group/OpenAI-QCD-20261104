import YM.QCD.Door.Flax
/-! # wipe weight. Hinge operators lists. -/
set_option maxHeartbeats 150000
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Grass Creek Ledge Function NormedSpace Finset Lat Kit
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator
variable {A B C D:Type*}[Fintype A][Fintype B][DecidableEq A][DecidableEq B]

lemma wipe_zero (U:Matrix A A ℂ)(V: Matrix B B ℂ)(x:Dirac (A⊕B)): wipe A B 0 (disguise (whole U V) x)=disguise V (wipe A B 0 x):=by
   refine AlgHom.congr_fun (φ₁:=(wipe A B 0).comp (disguise (whole U V))) (φ₂:=(disguise V).comp (wipe A B 0)) (ext_atoms fun j=> ?_) x
   rcases splits_index j with ⟨i,rfl⟩|⟨i,rfl⟩
   · simp only [AlgHom.comp_apply]; nth_rw 1 [show atom (head A B i)=near A B (atom i) from (embed_atom (head A B) i).symm]; rw [partitioned,wiper]; unfold disguise adapter; rw [change_atom,map_sum,map_sum]; simp_rw [map_smul,show ∀ j: Pairs A, near A B (atom j) = atom (head A B j) from fun j=> embed_atom (head A B) j,wiper]; simp
   simp only [AlgHom.comp_apply,tails]; -- bank
   change wipe A B (0) _= _; rw [show atom (tail A B i)=far A B (atom i) from (embed_atom (tail A B) i).symm,partitioned']; exact meadow ..
lemma dryG (x:Dirac (A ⊕ B)): wipe A B 0 (surf _ x) = surf B (wipe A B 0 x):=by
  have h (i:Pairs (A ⊕ B)): wipe A B 0 (surf _ (atom i))=surf _ (wipe A B 0 (atom i)):=by
    rcases splits_index i with ⟨i,rfl⟩|⟨i,rfl⟩
    · rw [wiper]; cases i
      next j=> change wipe A B 0 (surf _ (psi _))=_; rw [surf_P]; change wipe A B 0 (atom (head A B (.inr j)))=_; rw [wiper]; simp
      next j=> change wipe A B 0 (surf _ (bar _))=_; rw [surf_M,map_neg]; change -wipe A B 0 (atom (head A B (.inl j)))=_; rw [wiper]; simp
    rw [tails]; cases i
    next j=> change wipe A B 0 (surf _ (psi _))=surf _ (psi _); rw [surf_P,surf_P]; exact tails A B 0 (.inr j)
    next j=> change wipe A B 0 (surf _ (bar _))=surf _ (bar _); rw [surf_M,surf_M,map_neg]; exact congr_arg Neg.neg (tails A B 0 (.inl j))
  have he (i:List _): wipe A B 0 (surf _ (i.map atom).prod)=surf _ (wipe A B 0 (i.map atom).prod):=by induction i with
  | nil=> simp [surf_one]
  | cons j l ih=> rw [List.map_cons,List.prod_cons,surf_mul,map_mul,map_mul,surf_mul,ih,h]
  have hp (i): wipe A B 0 (surf _ (mono i))=surf _ (wipe A B 0 (mono i)):=by obtain ⟨x,-,-,hx⟩:=expression i; rw [hx]; simpa only [List.map_ofFn] using he (List.ofFn x)
  rw [←write x]; simp only [map_sum,map_smul,map_smulₛₗ,hp]
lemma reins (V: Matrix A B ℂ)(K:Matrix B A ℂ)(x:Dirac (A⊕B)) : wipe A B (bladesF V K) x= wipe A B 0 (shear V K x):=by
  have hm:= skinny (0) (bladesF V K) x
  rw [zero_add, show birth (bark (bladesF V K)) x=shear V K x from DFunLike.congr_fun (shear_equals V K).symm x] at hm; exact hm.symm
lemma barkW (U:Matrix A A ℂ)(V:Matrix B B ℂ) (K:Matrix A B ℂ)(Z:Matrix B A ℂ)(h:U∈unitary _)(hv:V∈unitary _) (x:Dirac (A⊕B)): disguise V (wipe A B (bladesF (U*K* star V) (V*Z*star U)) x)=wipe A B (bladesF K Z) (disguise (whole U V) x):=by rw [reins,reins, ← wipe_zero,chop U V K Z 0 0 h hv]
lemma barkZ (K:Matrix A B ℂ)(Z:Matrix B A ℂ)(x:Dirac (A⊕B)): surf _ (wipe A B (bladesF K Z) x)=wipe A B (bladesF Zᴴ Kᴴ) (surf _ x):=by rw [reins,reins,← dryG,chili]

end YM.QCD.Sway
