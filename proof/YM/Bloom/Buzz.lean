import YM.Bloom.Shore
import YM.Play.Joints
import YM.QCD.Cove.Brash
/-! # thermal rows flavors. period and Spine. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.QCD.Bloom.Buzz
open Function Lattice Laurent Bloch Metric RG Filter Arise
open Finset YM.Bank Precision Matrix YM.Bloom
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free YM.Bloom.TreeP
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Kit
variable {c f:Side}{N j k m n i l b ℓ r:ℕ}{A J Y:Type}[Fintype A][Fintype J][Fintype Y]
-- spin HH left-link matrices.
variable (P Q : Parc)(a d:Fiber)(x y: Cover)(i j:Flavor N)
noncomputable def flaw (N:ℕ)(i: Flavor N)(P:Matrix Unit A ℂ): Matrix Unit (A× Flavor N) ℂ:= Matrix.of fun _ q=> if i=q.2 then P () q.1 else 0
lemma wing(i:Flavor N)(P:Matrix Unit A ℂ)(Q: Matrix A J ℂ): flaw N i P*choir N Q=flaw N i (P*Q):=by
    ext ⟨⟩ ⟨j,p⟩; rw [Matrix.mul_apply,Fintype.sum_prod_type]; by_cases hp:i=p
    · subst p; simp_rw [flaw,Matrix.of_apply,ite_mul,zero_mul,sum_ite_eq,mem_univ,if_true]; simp only [choir,Matrix.blockDiagonal_apply,if_true,Matrix.mul_apply]
    unfold flaw; simp [choir,hp,ite_mul,Matrix.blockDiagonal_apply]
lemma turnedV(i j:Flavor N)(P:Matrix Unit A ℂ)(Q:Matrix Unit A ℂ) : (flaw N i P*(flaw N j Q).transpose) () ()= if i=j then (P*Q.transpose) () () else 0:=by
    rw [Matrix.mul_apply,Fintype.sum_prod_type]; by_cases he:i=j <;> simp [flaw,ite_mul,mul_ite,eq_comm,he, Matrix.mul_apply]
noncomputable def scrim {A Y:Type} (F:Matrix Unit A ℂ) (G: Matrix Unit Y ℂ) : Matrix Unit (A⊕Y) ℂ:= Matrix.of fun _ j=> j.elim (fun i=> F () i) (fun i=>G () i)
lemma beam_a {X Y:Type}[Fintype X][Fintype Y] {Q : Matrix A J ℂ} {R : Matrix X Y ℂ}(P:Matrix Unit A ℂ)(S: Matrix Unit X ℂ) : scrim P S * fromBlocks Q 0 0 R = scrim (P*Q) (S*R) :=by ext i j; rcases i with ⟨⟩; cases j <;> simp only [Matrix.mul_apply,Fintype.sum_sum_type,scrim,of_apply,fromBlocks_apply₁₁,fromBlocks_apply₂₂, fromBlocks_apply₁₂,fromBlocks_apply₂₁,Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr,mul_zero,sum_const_zero, add_zero,zero_add]
lemma beam_b {X Y:Type}[Fintype X][Fintype Y] {R : Matrix A Y ℂ}(P:Matrix Unit A ℂ)(S: Matrix Unit X ℂ): scrim P S* fromBlocks (0:Matrix A J ℂ) R (0:Matrix X J ℂ) (0:Matrix X Y ℂ) = scrim 0 (P*R) :=by
    ext i j; rcases i with ⟨⟩; cases j <;> simp only [Matrix.mul_apply,Fintype.sum_sum_type,scrim,of_apply,fromBlocks_apply₁₁,fromBlocks_apply₂₂, fromBlocks_apply₁₂,fromBlocks_apply₂₁,Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr,mul_zero,zero_mul,sum_const_zero, add_zero,zero_add]
lemma beam_dot (P R:Matrix Unit A ℂ)(Q S: Matrix Unit Y ℂ): (scrim P Q*(scrim R S).transpose)= P*R.transpose+Q*S.transpose:=by ext i j; rcases i with ⟨⟩; obtain ⟨⟩:=j ; simp only [Matrix.mul_apply,Matrix.transpose_apply, Fintype.sum_sum_type,Matrix.add_apply,scrim,of_apply, Sum.elim_inl, Sum.elim_inr]
noncomputable def paint (c:Side)(x:Cover)(a:Fiber)(i:Flavor N)(P:Parc) (b:Bool): Matrix Unit (Keys c N) ℂ:= let F:= flaw _ i (plume c x a P); if b then scrim 0 F else scrim F 0
noncomputable def start (f: Side)(d:Train r)(N:ℕ) : Matrix (Keys f N) (Keys f N) ℂ:= stamping (choir N (stage d f))
-- X spin bars actual † lifted. transpose sparse. cumulative.L.
noncomputable def wheel (U:Kit.Rail f c)(X:Kit.Rail c f) (N:ℕ) := bladesF (choir N U) (choir N X)
lemma neg_wheel (U:Kit.Rail f c)(X:Kit.Rail c f) : paint f x a i P false*wheel U X N=scrim (flaw _ i (plume f x a P*U)) (0:Matrix Unit (Modes c N) ℂ):=by unfold paint wheel bladesF; simp only [Bool.false_eq_true,↓reduceIte]; rw [beam_a, Matrix.zero_mul, wing]
lemma transpose_p {V:Matrix A J ℂ} : (choir N V).transpose=choir N V.transpose:=by ext ⟨a,b⟩ ⟨v,z⟩; by_cases ht:b=z<;> simp[ht,choir,Matrix.blockDiagonal_apply,eq_comm]
lemma pos_wheel (U: Kit.Rail f c)(X:Kit.Rail c f): paint f x a i P true *wheel U X N=scrim (0:Matrix Unit (Modes c N) ℂ) (flaw _ i (plume f x a P*X.transpose)):=by unfold paint wheel bladesF; simp only [↓reduceIte]; rw [beam_a,Matrix.zero_mul,transpose_p,wing]
lemma slice_read (V: Sheet f)(q w:Bool): (paint f x a i P q * stamping (choir N V)*(paint f y d j Q w).transpose) () ()= if (q=false∧ w=true ∧ i=j) then pairS f V x y a d P Q else 0:=by
   unfold pairS paint stamping; dsimp only; cases q <;> cases w <;> simp only [Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,false_and,and_false,true_and,beam_b,beam_dot,Matrix.zero_mul,zero_add,transpose_zero,Matrix.mul_zero,Matrix.zero_apply]
   rw [wing,turnedV,spoon]
lemma rotor {V:Sheet c}{U: Kit.Rail f c}{X:Kit.Rail c f}: wheel U X N*stamping (choir N V)*(wheel U X N).transpose= stamping (choir N (U*V*X)):=by
    unfold wheel stamping bladesF; rw [choir_mul,choir_mul, Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]; simp
lemma norms_pig (V:Kit.Rail c f) (J:Matrix Unit (Lat.Row f) ℂ)(h:∀ i,star (J () i)=J () i) (x): ‖(J*V.transpose) () x‖=‖(J*Vᴴ) () x‖:= by
    rw [← norm_star ((J*V.transpose) () x)]; congr 1; rw [Matrix.mul_apply,Matrix.mul_apply,star_sum]; refine sum_congr rfl fun i _=>by rw [star_mul,h]; exact mul_comm ..
lemma paint_budget {m:ℕ}(hp:P∈tails k n)(hm:n+2 ≤ m): ∃ C:ℝ,0≤ C ∧∀ {c f:Side} (u:Flavor N)(x:Cover)(a:Fiber)(b:Bool)(g: Ratio c f)(D B: Train m){U X Q}, Giant m g D B U X Q → ∀ i, ‖(paint f x a u P b*wheel U X N) () i‖ ≤ C*gear g.count k:=by
    obtain ⟨C,hc,h⟩:=valves _ hp hm; refine ⟨C,hc,fun {c f} u x a b g D B {U X Q} H i=>?_⟩; have h':0 ≤ C* gear g.count k:=mul_nonneg hc (gear_pos ..).le; cases b <;> cases i
    next i=> rw [neg_wheel,scrim,of_apply]; simp only [Sum.elim_inl]; unfold flaw; rw [Matrix.of_apply]; split; exact (h _ _ _ H ..).1; exact ((norm_zero).le.trans h')
    next i=> rw [neg_wheel,scrim,of_apply]; exact ((norm_zero).le.trans h')
    next i=> rw [pos_wheel,scrim,of_apply]; exact ((norm_zero).le.trans h')
    next i=> rw [pos_wheel,scrim,of_apply]; simp only [Sum.elim_inr]; unfold flaw; rw [Matrix.of_apply]; split; rw [norms_pig]; exact (h _ _ _ H ..).2; exact furls x P a; exact ((norm_zero).le.trans h')
lemma sailS {n m:ℕ}(hp:P∈ tails k ℓ)(hq:Q∈tails r n)(he:ℓ+2 ≤ m)(hu:n+2 ≤ m): ∃ C:ℝ,0 ≤ C ∧∀ {c f:Side} (i j: Flavor N)(x y:Cover)(a b:Fiber)(q w:Bool)(g: Ratio c f)(D B:Train m){U X W}, Giant m g D B U X W →
    ‖(paint f x a i P q*(wheel U X N*start c B N*(wheel U X N).transpose)*(paint f y b j Q w).transpose) () ()‖ ≤ C*(gear g.count k*gear g.count r):=by
       obtain ⟨C,hc,h⟩:=mariner P Q hp hq he hu; refine ⟨C,hc,fun {c f} i j x y a b q w g D B {U X W} H=>?_⟩; unfold start; rw [rotor,slice_read]; split; · exact h _ _ _ H ..
       rw [norm_zero]; exact mul_nonneg hc (mul_nonneg (gear_pos ..).le (gear_pos ..).le)
-- sailS at unit means full self if D.F rank kept
end YM.QCD.Bloom.Buzz
#print axioms YM.QCD.Bloom.Buzz.sailS
#print axioms YM.QCD.Bloom.Buzz.paint_budget
