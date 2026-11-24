import YM.Heron.Quack
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Arise.Range
open Maxwell.Free (fromCenter)
open Finset
variable {d:ℕ}(α β:letters d)(α':letters 8)(x:Points 2)(y:E4)(hx:x∈conf 2)(h:Points.cons y x∈conf 3)
local notation "T"=> letters d
local notation "I"=> letters 8
abbrev oakT(d:ℕ) (_ : Fin 2):= d
abbrev hill(d:ℕ): Fin 3→ℕ:= Fin.cons 8 (oakT d)
local notation "fo"=>oakT d
local notation "H"=>hill d
local notation "A"=> chime (hill d) (Points.cons y x)
local notation "B"=> chime (oakT d) x
abbrev Dot(d:ℕ):= Fin 2×letters d
noncomputable def west (d:ℕ)(q:Dot d): Seed (Occ (hill d)):= rifle (hill d) q.1.succ (thetaBasis _ q.2)
noncomputable def east (d:ℕ)(q:Dot d): Seed (Occ (oakT d)):= rifle (oakT d) q.1 (thetaBasis _ q.2)
-- θ fish
noncomputable def tipR(d:ℕ)(v: I) : Seed (Occ (hill d)):= rifle (hill d) 0 (thetaBasis _ v)
local notation "D'"=> tipR d
include h hx
lemma strap(u v: Dot d): unionB A (west d u) (west d v)= unionB B (east d u) (east d v):=by
     unfold west east; rw[mounted,mounted,mounted,mounted,sector _ h,sector _ hx]; simp only [UV.Free.pair, Fin.succ_inj]; split <;> first|rfl|skip
lemma drink(w:Dot d) (p:I) : unionB A (tipR d p) (west d w) = -linked (x w.1) y w.2 p:=by
     unfold tipR west; rw [mounted,mounted,sector _ h]; simp only [UV.Free.pair, if_neg (Ne.symm (Fin.succ_ne_zero _))]; obtain ⟨a,u|u⟩ := w <;> (rcases p with q|q) <;> simp [linked] <;> rfl
lemma auxili(s:List (Dot d)):lease A (pwn (s.map (west d))) = lease B (pwn (s.map (east d))):=by
    induction ht : s.length using Nat.strong_induction_on generalizing s with
    | h k ih=>
        subst k; cases s with
        | nil=> change lease _ 1=lease _ 1; rw[clean1,clean1]
        | cons a s =>
             change lease A (line (west d a) * pwn (s.map (west d)))=lease B (line (east d a)*pwn (s.map (east d))); rw[slipH,slips_map,slipH,slips_map]; unfold slips; refine sum_congr rfl fun i _=>?_ ; dsimp only; rw[strap x y hx h, ih _ _ _ rfl]; exact lt_trans (Maxwell.Free.pulls_short i) (by simp)
variable (p q:GPol)(u v:List (letters d)) (F:SpinPol 8)(t r:T)
local notation "U"=> Hail.tagD u
local notation "V"=> Hail.tagD v
noncomputable def fiesta (x:Points 2)(s:List (Dot d)) := lease (chime (oakT d) x) (pwn (s.map (east d)))
noncomputable def joiner(w: Fin 2)(u:List (letters d)):=u.map fun i=> (w,i)
noncomputable def tot(u v:List (letters d)):= joiner 0 u ++ joiner 1 v
local notation "M"=> Maxwell.Wick.moment su
noncomputable def triangle(y:E4)(x:Points 2)(f:Pol 8)(g:Fin 2→Pol d):ℂ:= UV.Free.moment (hill d) (Points.cons y x) (Fin.cons f g)
noncomputable def trioL (y:E4)(x:Points 2)(g:Fin 2→Pol d): Pol 8→ₗ[ℂ]ℂ := (UV.Free.moment (hill d) (Points.cons y x)).toLinearMap (Fin.cons 0 g) 0
lemma trip(W:Pol 8)(g:Fin 2→Pol d): trioL y x g W= triangle y x W g:=by
    change UV.Free.moment H (Points.cons y x) (update (Fin.cons (α:=fun i:Fin 3=>Pol (H i)) 0 g) 0 W)=_; exact congr_arg (fun p:(i:Fin 3)→Pol (H i)=>UV.Free.moment H (Points.cons y x) p) (Fin.update_cons_zero ..)
lemma front : ∀ (i:Fin 2), twig H i.succ (Hail.tagD u)=pwn ((joiner i u).map (west d)):=by
    intro i; induction u with
    | nil=> exact map_one _
    | cons a s ih=> exact (map_mul (twig H i.succ) (atom a) (Hail.tagD s)).trans (congr_arg₂ (·*·) (show twig H i.succ _= line (west d (i,a)) from ExteriorAlgebra.map_apply_ι (rifle H i.succ) _) ih)
lemma tonic : ∀ (i:Fin 2), twig (oakT d) i (Hail.tagD u)=pwn ((joiner i u).map (east d)):=by
    intro i; induction u with
    | nil=> exact map_one _
    | cons a s ih=> change twig fo i (atom a* Hail.tagD s)= _; rw [map_mul,ih]; change _ = line (east d _) * pwn ((joiner i s).map _); exact congr_arg (·* pwn ((joiner i s).map (east d))) (ExteriorAlgebra.map_apply_ι (rifle _ _) _)
omit h hx
lemma rows (r s:List (Seed (Occ H))) : pwn (r++s) = pwn r*pwn s:=by simp [pwn]
include hx h
lemma build(W:GPol):trioL y x (![(p⊗ₜ[ℂ] U),q⊗ₜ[ℂ] V]) (W⊗ₜ[ℂ] F) = M (Points.cons y x) (![Maxwell.reduceEq W, Maxwell.reduceEq p, Maxwell.reduceEq q])*lease A (twig H 0 F*pwn ((tot u v).map (west d))) :=by
     rw[trip x y hx h]; unfold triangle; let G:Fin 3→GPol:=![W,p,q]; let P:(i:Fin 3)→SpinPol (H i):= Fin.cons F (![U,V]);
     refine Eq.trans (?_:_= moment H (Points.cons y x) (fun i=>G i ⊗ₜ[ℂ] P i)) ((stroll _ h G P).trans (?_)); · apply congr_arg; funext i; fin_cases i<;>rfl
     refine congr_arg₂ (·*·) ?_ ?_; · apply congr_arg; funext i; fin_cases i<;>rfl
     apply congr_arg; rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_cons,List.prod_singleton]; change twig H 0 F*(twig H (Fin.succ 0) U * twig H (Fin.succ 1) V)=_; unfold tot; rw [List.map_append,rows,front x y hx h u (0:Fin 2), front x y hx h v (1:Fin 2)]
noncomputable def ear (x:Points 2) (p r:Pol d):ℂ:= moment (oakT d) x (![p,r])
lemma seedG : ear x (p⊗ₜ[ℂ]U) (q⊗ₜ[ℂ] V)= M x (![Maxwell.reduceEq p,Maxwell.reduceEq q])* fiesta x (tot u v):=by
     let g:Fin 2→ GPol:=![p,q]; let e:(i:Fin 2)→SpinPol (oakT d i):= ![U,V]; unfold ear; rw [show _ = _ from (show (![(p⊗ₜ[ℂ]U),q⊗ₜ[ℂ] V])=(fun i=> g i ⊗ₜ[ℂ] e i) from (by funext i;fin_cases i<;>rfl)),stroll x hx g e]; refine congr_arg₂ (·*·) ?_ ?_; · apply congr_arg; funext i; fin_cases i<;>rfl
     unfold fiesta; apply congr_arg; rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_singleton]; change twig fo (0: Fin 2) U *twig fo 1 V=_; rw [tonic x y hx h u 0,tonic x y hx h v 1]; unfold tot pwn; rw [List.map_append,List.map_append,List.prod_append]
end YM.Heron
#print axioms YM.Heron.strap
#print axioms YM.Heron.build
#print axioms YM.Heron.seedG
