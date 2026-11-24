import YM.QCD.Stew.Life
import YM.MassiveQCD.Palette.Symmetry
/-! # Matrix representation for the Lie-flat bill after splitting.
All flavors, vector-torus conjugation. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
namespace Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {t:ℝ} {o: Site c}
variable {D K:Type*} [Fintype D][DecidableEq D][Fintype K][DecidableEq K]
local notation "J"=> Modes c N
local notation "V"=> EvenA c N
lemma rank_two (x:V) (h:AccentFit x): panel 2 x.val=form (grasp x.val):=by
 
   let p:= Complex.I • (1:Matrix (Flavor N) (Flavor N) ℂ); have hp:p∈unitary _:=unitaryV Complex.I _ (by simp)
   have hh: disguise (Complex.I • (1:Matrix J J ℂ)) x.val=x.val:=by
      have hv:flute (Lat.Row c) p=Complex.I • (1:Matrix J J ℂ):=by
         ext ⟨a,i⟩ ⟨b,j⟩; by_cases hf:a=b<;> by_cases hg:i=j<;> simp [p,flute, hf,hg,Matrix.smul_apply]
      have he:= h _ ⟨hp, fun i j hi=>by simp [p,Matrix.one_apply_ne hi, Matrix.smul_apply]⟩; rw [hv] at he; exact congr_arg Subtype.val he
   exact kent x.val (unbalanced _ hh) -- syntax
lemma adapted (L:Matrix J J ℂ)(x:V)(h: AccentFit x): grasp (disguise L x.val)= star L * grasp x.val * L:=by rw [←breast, sport,rank_two x h, disguise, form_map,Matrix.transpose_transpose,gravid,Matrix.mul_assoc]
lemma mirror (L:Matrix J J ℂ)(x:V)(h: AccentFit x): grasp (disguise L (surf _ x.val))= star L*star (grasp x.val)*L:=by rw [←breast,sport,toned, rank_two x h,Port.surf_form,disguise, form_map, Matrix.transpose_transpose,gravid,Matrix.mul_assoc]
lemma construe (x: V)(h:AccentFit x)(L:Matrix (Flavor N) (Flavor N) ℂ)(he:Chord L) : Commute (flute (Lat.Row c) L) (grasp x.val):=by
   let M:=flute (Lat.Row c) L; have hg : disguise M x.val=x.val:=congr_arg Subtype.val (h L he)
   have he':= adapted M x h; rw [hg] at he'
   change M*grasp x.val= _; nth_rw 1 [he']; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,(unit_f he.1).2, one_mul] -- .1? Unit check

variable (p:Matrix (D×Flavor N) (D×Flavor N) ℂ)(h: ∀ L:Matrix (Flavor N) (Flavor N) ℂ,Chord L→ Commute (flute D L) p)
include h
lemma neutral_off {k l:Flavor N}(hk:k≠l)(i j:D): p (i,k) (j,l)=0:=by
   let R:Flavor N→ℂ:= fun i=> if k=i then -1 else 1; let L:= Matrix.diagonal R
   have hh:L∈unitary _:=by
       have hL : star L=L:=by
          ext a b; rcases eq_or_ne a b with hv|hv
          · subst b; simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,L,Matrix.diagonal_apply,if_true]; exact lines k a
          simp [hv,Ne.symm hv,L, R]
       have hp:L*L=1:=by ext a b; by_cases he:a=b <;> by_cases hh:k=b <;> simp [L, R,Matrix.one_apply,he,hh]
       constructor <;> rw [hL,hp]
   have hu:= congr_fun (congr_fun ((h _ ⟨hh,fun i j hi=>by simp [L,hi]⟩).eq) (i,k)) (j,l)
   have hx : -p (i,k) (j,l)=p (i,k) (j,l):=by simpa [Matrix.mul_apply,flute,Matrix.kronecker_apply,L, Fintype.sum_prod_type, Matrix.one_apply, Matrix.diagonal_apply, mul_ite,ite_mul,R,hk] using hu
   apply Complex.ext; · have hp:=congr_arg Complex.re hx; rw [Complex.neg_re] at hp; rw [Complex.zero_re]; linarith
   have hp:=congr_arg Complex.im hx; rw [Complex.neg_im] at hp; rw [Complex.zero_im]; linarith
omit h
lemma phases (v:V)(h:AccentFit v) : grasp v.val=Matrix.blockDiagonal (fun i:Flavor N=>feeF i v):=by
     ext ⟨i,k⟩ ⟨j,l⟩; rw [Matrix.blockDiagonal_apply]; split
     next h=> change k=l at h; subst k; rfl
     next he=> exact neutral_off (grasp v.val) (construe v h) he _ _
lemma rite (v:V)(b : Flavor N)(X: Sheet c)(h:AccentFit v): feeF b (sways (copies N X) v)=star X * feeF b v*X:=by
   let T:=copies N X; have he:=adapted T v h; rw [phases v h] at he; unfold T at he; rw [copies,Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul] at he
   ext i j; change grasp _ (i,b) (j,b)=_; exact (congr_fun (congr_fun he (i,b)) (j,b)).trans (by simp only [Matrix.blockDiagonal_apply, ↓reduceIte]; rfl)
lemma burst (v:V)(b: Flavor N)(h:AccentFit v): feeF b (Regal c N v)=star (chirality c)*star (feeF b v)*chirality c:=by
   let X:=chirality c; have he:=mirror (copies N X) v h; rw [phases v h,copies,Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose,Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul] at he
   ext i j; change grasp _ (i,b) (j,b)=_; exact (congr_fun (congr_fun he (i,b)) (j,b)).trans (by simp only [Matrix.blockDiagonal_apply, ↓reduceIte]; rfl)
end Phased
end YM.QCD.Stew
