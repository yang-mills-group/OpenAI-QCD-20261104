import YM.MassiveQCD.Palette.Phased
import YM.QCD.Stew.Payday
/-! # Vector-phase matrices and sharp block capsule.
 `flash` projects onto a single component with true guise equivariance (for color,
 five and rotations, each including a negative sign and nonstandard spin if Warrant).
 No placeholders for unit-F covariance (waves already handle their contact terms).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k:ℕ} {t:ℝ} {o: Site c}
variable {D K:Type*} [Fintype D][DecidableEq D][Fintype K][DecidableEq K]
section matrix
abbrev FlavorF (N:ℕ) (c:Side):= Flavor N → Sheet c
noncomputable def paneF (M: FlavorF N c): EvenA c N:=⟨form (Matrix.blockDiagonal M), form_plus _⟩
lemma tidyF (M: FlavorF N c)(b:Flavor N): feeF b (paneF M)= M b:=by
   ext i j; change grasp (form (Matrix.blockDiagonal M)) (i,b) (j,b)=_; rw [gravid]; exact Matrix.blockDiagonal_apply_eq M i j b -- syntax
lemma plankGrade (M: FlavorF N c): coef ∅ (paneF M).val=0:=spectrum (Grass.form_two _) _ (by simp)
noncomputable def meterF (c:Side)(N:ℕ): FlavorF N c→ₗ[ℂ]EvenA c N:={
   toFun:=paneF
   map_add':=fun M W=> Subtype.ext (by change form (Matrix.blockDiagonal (M+W))= _; rw [Matrix.blockDiagonal_add,form_add]; rfl)
   map_smul':=fun s M=>Subtype.ext (by change form (Matrix.blockDiagonal (s • M))=s • _; rw [Matrix.blockDiagonal_smul]; unfold paneF; simp only [form,Matrix.smul_apply, smul_eq_mul,mul_smul, Finset.smul_sum]) } -- "unfold paneF" tgt? check.
lemma pageS (M W:FlavorF N c)(X:Matrix (Modes c N) (Modes c N) ℂ)(hv:X∈unitary _)(h: Matrix.blockDiagonal M*X=X*Matrix.blockDiagonal W): sways X (paneF M)=paneF W:=by
   apply Subtype.ext; change disguise _ (form _) = form _; rw [disguise,form_map,Matrix.transpose_transpose,h,← Matrix.mul_assoc,hv.1,one_mul]
lemma page (M W:FlavorF N c)(X: Sheet c)(hX:X∈unitary _)(he:∀ b,M b*X=X*W b): sways (copies N X) (paneF M)=paneF W:=by
   refine pageS M W _ (copies_unitary _ _ hX) ?_; unfold copies; rw [← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]; exact congr_arg Matrix.blockDiagonal (funext he)
lemma pageK (M:FlavorF N c): AccentFit (paneF M):=by
     intro P h; apply pageS M M _ (unit_f h.1); let I:=(flute (Lat.Row c) P); have he : I=Matrix.blockDiagonal (fun k:Flavor N=> P k k • (1: Sheet c)):=by
         ext ⟨x,y⟩ ⟨w,v⟩; unfold I; by_cases hx:x=w <;> by_cases hv:y=v
         all_goals simp only [flute, Matrix.blockDiagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; simp [hx,hv,h.2]
     change Matrix.blockDiagonal M*I=I*Matrix.blockDiagonal M; rw [he,← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]; refine congr_arg _ (funext (fun i=>?_)); simp
lemma pageStar (M:FlavorF N c): Regal c N (paneF M)= paneF (fun b=>chirality c *star (M b)*chirality c):=by
   apply Subtype.ext; change disguise (copies N (chirality c)) (surf _ (form _))= form _; rw [surf_form,disguise,form_map,Matrix.transpose_transpose,← Matrix.mul_assoc,← copies_star, chi_star, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose]; unfold copies; rw [← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]; rfl -- ambiguity
lemma capsule (M:FlavorF N c)(U:Support c)(h:∀ b i j,i∉U∨j∉U → cell (M b) i j=0) : Gated U (paneF M):=by
    unfold Gated; let T:= Matrix.blockDiagonal M; change form T∈_; unfold form; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.sum_mem; intro j _; by_cases hp:i.1.1∈U ∧ j.1.1∈U
    · apply Subalgebra.smul_mem; apply Subalgebra.mul_mem <;> apply Creek.marked
      exacts [mem_filter.mpr ⟨mem_univ _,hp.2⟩,mem_filter.mpr ⟨mem_univ _,hp.1⟩]
    rw [show T i j=0 from ?_, zero_smul]; exact Subalgebra.zero_mem _
    unfold T; rw [Matrix.blockDiagonal_apply]; split; · exact Matrix.ext_iff.mpr (h _ _ _ (by tauto)) i.1.2 j.1.2
    rfl
end matrix
-- canonical projection & cuts. Caller uses any Θ.
noncomputable def beam (o:Site c)(M:Flavor N→ Spike):EvenA c N := paneF (fun i=> localX o (M i))
lemma flashPad (f:Flavor N→Spike) {U:Support c}(h:o∈U): Gated U (beam o f):=by
    refine capsule _ _ ?_; intro b i j he; rw [placed]; split
    next hh=> rcases hh with ⟨rfl,rfl⟩; tauto
    next _=> rfl
lemma flashColor (o:Site c)(f:Flavor N→Spike): shadeG (fun _: Grid c=>beam o f):= fun _ g => congr_arg Subtype.val (page _ _ (siteRot g) (siteRot_u g) (fun b=>(commG o (f b) g).symm.eq))
lemma flashTwist (o:Site c)(v:Strut c)(k:Spike)(g:Site c→ℂ)(f:Flavor N→Spike) (he: Warrant v g k) : Diode N v k g (beam o f) = beam (act v o) (fun b=>k*f b*star k):=page _ _ (haze v k g) (trail he) (fun b=> principal o (f b) he)
lemma flashStar (o:Site c)(f:Flavor N→Spike): Regal c N (beam o f)=beam o (fun b=>g5*star (f b)*g5):= (pageStar _).trans (congr_arg paneF (funext (fun b=> (tiltE o (f b) none (1:Grid c)).symm)))
lemma flashAt (o:Site c)(f:Flavor N→Spike)(b:Flavor N): shape o (feeF b (beam o f)) none=f b :=by rw [beam,tidyF,show _=_ from atO o (f b) none]; simp -- atO sig
end YM.QCD.Stew.Phased
